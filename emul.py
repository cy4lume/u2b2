import argparse
from copy import deepcopy
from capstone import (
    CS_OP_IMM,
    CS_OP_MEM,
    CS_OP_REG,
    CS_ARCH_MIPS,
    CS_MODE_MIPS32,
    CS_MODE_BIG_ENDIAN,
    Cs,
    CsInsn
)
import capstone.mips_const as mips
from elftools.elf.elffile import ELFFile
from unicorn import (
    Uc,
    UC_ARCH_MIPS,
    UC_MODE_MIPS32,
    UC_MODE_BIG_ENDIAN,
    UC_PROT_READ,
    UC_PROT_WRITE,
    UC_PROT_EXEC,
    UC_HOOK_CODE
)
from unicorn.mips_const import UC_MIPS_REG_SP, UC_MIPS_REG_PC
import z3

from exceptions import EmulatorStop
from state import Memory, Registers
from symbol import get_symbol_table, LibcSym
from symlibc import Libc as libc
from syscall import get_syscall_handler, handle_sys_exit


PAGE_SIZE = 0x1000
MAGIC_RETURN = 0x42424242
STACK_TOP = 0x7fff0000
STACK_SIZE = PAGE_SIZE

MAX_ARGC = 32
MAX_ARG_LEN = 1024
MAGIC_ARG = 0x42000000

EXCLUDE_FUNCS = ('__libc_csu_fini', '__libc_csu_init')


def align_down(addr, align=PAGE_SIZE):
    return addr & ~(align - 1)


def align_up(addr, align=PAGE_SIZE):
    return (addr + align - 1) & ~(align - 1)


def parse_operand(insn: CsInsn):
    for op in insn.operands:
        if op.type == CS_OP_REG:
            yield (op.reg)
        elif op.type == CS_OP_IMM:
            yield (op.imm)
        elif op.type == CS_OP_MEM:
            mem = op.mem
            yield (mem.disp, mem.base)
        else:
            raise ValueError("what?!")


def extract_array_store(model, expr):
    result = {}
    while expr.decl().name() == 'store':
        addr = expr.arg(1)
        val = expr.arg(2)
        addr_val = model.eval(addr, model_completion=True)
        val_val = model.eval(val, model_completion=True)
        result[int(str(addr_val))] = val_val
        expr = expr.arg(0)
    if expr.decl().name() == 'const':
        default = expr.arg(0)
    else:
        default = 0
    return result, default


def get_unexecuted_ranges(start, end, executed_addrs):
    unexec = [addr for addr in range(start, end) if addr not in executed_addrs]
    ranges = []
    for addr in unexec:
        if not ranges or addr != ranges[-1][1] + 1:
            ranges.append([addr, addr])
        else:
            ranges[-1][1] = addr
    return ranges


class Mips32Emulator:
    def __init__(self, path: str, verbose: bool):
        self.elf = None
        self.debug = False
        self.verbose = verbose

        uc = Uc(UC_ARCH_MIPS, UC_MODE_MIPS32 | UC_MODE_BIG_ENDIAN)
        md = Cs(CS_ARCH_MIPS, CS_MODE_MIPS32 | CS_MODE_BIG_ENDIAN)
        md.detail = True

        self.uc = uc
        self.md = md

        self.conditions = []
        self.terms = []

        self.regs = Registers()
        self.memory = Memory()

        self.functions = []

        self.entry, self.memory_init = self.read_elf(path)
        self.libc = LibcSym(self.uc, "./libs/mips-linux-gnu/lib")

        uc.mem_map(align_down(STACK_TOP - STACK_SIZE),
                   STACK_SIZE, UC_PROT_READ | UC_PROT_WRITE)
        uc.hook_add(UC_HOOK_CODE, self.hook_instr)

    def read_elf(self, path: str):
        self.elf = ELFFile(open(path, "rb"))
        for i in self.elf.get_dwarf_info().iter_CUs():
            self.debug = True
            break
        memory = Memory()
        uc = self.uc

        self.global_table = get_symbol_table(self.elf)
        found_main = False
        for symbol in self.elf.get_section_by_name('.symtab').iter_symbols():
            if symbol.name == 'main':
                if symbol['st_info']['type'] == 'STT_FUNC':
                    self.main_address = symbol['st_value']
                    found_main = True

            if symbol['st_info']['type'] == 'STT_FUNC':
                start = symbol['st_value']
                size = symbol['st_size']
                end = start + size

                if size == 0 or symbol.name in EXCLUDE_FUNCS:
                    continue

                self.functions.append({
                    'name': symbol.name,
                    'start': start,
                    'end': end,
                    'dead': [],
                    'executed': False
                })
        if not found_main:
            print("Is This stripped binary?")

        # sp todo

        got_ranges = []
        for sec in self.elf.iter_sections():
            if sec.name.startswith('.got'):
                start = sec['sh_addr']
                end = start + sec['sh_size']
                got_ranges.append((start, end))

        def in_got(addr):
            return any(start <= addr < end for start, end in got_ranges)

        for seg in self.elf.iter_segments():
            if seg["p_type"] != "PT_LOAD":
                continue

            vaddr = seg["p_vaddr"]
            memsz = seg["p_memsz"]
            filesz = seg["p_filesz"]
            data = seg.data()

            base = align_down(vaddr)
            top = align_up(vaddr + memsz)
            size = top - base

            uc.mem_map(base, size, UC_PROT_READ |
                       UC_PROT_WRITE | UC_PROT_EXEC)

            # Write in memory
            for addr in range(vaddr, vaddr + memsz, 4):
                if in_got(addr):  # ignore got sections
                    continue
                offset = addr - vaddr
                seg = data[offset:offset+4]
                if len(seg) == 0:
                    seg = b"\x00" * 4
                memory.store(addr, int.from_bytes(seg, "big"))

            uc.mem_write(vaddr, data)
            if memsz > filesz:
                uc.mem_write(
                    vaddr + filesz, b"\x00" * (memsz - filesz))

            for arg_i in range(MAX_ARGC):
                memory.store(STACK_TOP - 4 * (MAX_ARGC - arg_i),
                             MAGIC_ARG + MAX_ARG_LEN * arg_i)

        return (self.elf.header["e_entry"], memory)

    def hook_instr(self, uc: Uc, address: int, size: int, user_data):
        if self.type == "trace":
            self.coverage.add(address)

        md = self.md
        uc.reg_write(UC_MIPS_REG_PC, address + 4)

        insn_bytes = uc.mem_read(address, size)
        for insn in md.disasm(insn_bytes, address):
            if self.verbose:
                print(insn)
            self.handle_insn(insn)

    def check_overflow():
        # not yet
        pass

    def handle_insn(self, insn: CsInsn):
        REGS = self.regs
        MEMORY = self.memory

        operands = list(parse_operand(insn))
        match insn.id:
            case mips.MIPS_INS_ADD:
                rd, rs, rt = operands
                REGS[rd] = REGS[rs] + REGS[rt]
                self.check_overflow()

            case mips.MIPS_INS_SUB:
                rd, rs, rt = operands
                REGS[rd] = REGS[rs] - REGS[rt]

            case mips.MIPS_INS_ADDU:
                rd, rs, rt = operands
                REGS[rd] = REGS[rs] + REGS[rt]

            case mips.MIPS_INS_SUBU:
                rd, rs, rt = operands
                REGS[rd] = REGS[rs] - REGS[rt]

            case mips.MIPS_INS_MUL:
                rs, rt = operands

                rs = z3.SignExt(32, REGS[rs])
                rt = z3.SignExt(32, REGS[rt])
                prod = rs * rt

                lo = z3.Extract(31,  0, prod)
                hi = z3.Extract(63, 32, prod)

                REGS[mips.MIPS_REG_LO] = lo
                REGS[mips.MIPS_REG_HI] = hi

            case mips.MIPS_INS_MULT:
                rd, rs, rt = operands
                REGS[rd] = REGS[rs] * REGS[rt]

            case mips.MIPS_INS_DIV:
                rs, rt = operands

                lo = REGS[rs] / REGS[rt]
                hi = REGS[rs] % REGS[rt]

                REGS[mips.MIPS_REG_LO] = lo
                REGS[mips.MIPS_REG_HI] = hi

            case mips.MIPS_INS_AND:
                rd, rs, rt = operands
                REGS[rd] = REGS[rs] & REGS[rt]

            case mips.MIPS_INS_OR:
                rd, rs, rt = operands
                REGS[rd] = REGS[rs] | REGS[rt]

            case mips.MIPS_INS_XOR:
                rd, rs, rt = operands
                REGS[rd] = REGS[rs] ^ REGS[rt]

            case mips.MIPS_INS_NOR:
                rd, rs, rt = operands
                REGS[rd] = ~(REGS[rs] | REGS[rt])

            case mips.MIPS_INS_LW:
                rd = operands[0]
                pc, rs = operands[1]
                REGS[rd] = MEMORY.load(REGS[rs] + pc)

            case mips.MIPS_INS_LH:
                rd = operands[0]
                pc, rs = operands[1]
                addr = REGS[rs] + pc
                addr_round = addr & z3.BitVecVal(~0b11, 32)
                if z3.is_expr(addr_round):
                    addr_round = z3.simplify(addr_round)
                offset = addr & 0b11
                if z3.is_expr(offset):
                    offset = z3.simplify(offset)
                
                hi = 31 - 8 * offset
                lo = 16 - 8 * offset
                if z3.is_expr(hi):
                    hi = z3.simplify(hi)
                    hi = hi.as_long()
                if z3.is_expr(lo):
                    lo = z3.simplify(lo)
                    lo = lo.as_long()
                
                REGS[rd] = z3.simplify(z3.SignExt(16, z3.Extract(hi, lo, MEMORY.load(addr_round))))
            
            case mips.MIPS_INS_LHU:
                rd = operands[0]
                pc, rs = operands[1]
                addr = REGS[rs] + pc
                addr_round = addr & z3.BitVecVal(~0b11, 32)
                if z3.is_expr(addr_round):
                    addr_round = z3.simplify(addr_round)
                offset = addr & 0b11
                if z3.is_expr(offset):
                    offset = z3.simplify(offset)
                
                hi = 31 - 8 * offset
                lo = 16 - 8 * offset
                if z3.is_expr(hi):
                    hi = z3.simplify(hi)
                    hi = hi.as_long()
                if z3.is_expr(lo):
                    lo = z3.simplify(lo)
                    lo = lo.as_long()
                
                REGS[rd] = z3.simplify(z3.ZeroExt(16, z3.Extract(hi, lo, MEMORY.load(addr_round))))

            case mips.MIPS_INS_LB:
                rd = operands[0]
                pc, rs = operands[1]
                addr = REGS[rs] + pc
                addr_round = addr & z3.BitVecVal(~0b11, 32)
                if z3.is_expr(addr_round):
                    addr_round = z3.simplify(addr_round)
                offset = addr & 0b11
                if z3.is_expr(offset):
                    offset = z3.simplify(offset)
                
                hi = 31 - 8 * offset
                lo = 24 - 8 * offset
                if z3.is_expr(hi):
                    hi = z3.simplify(hi)
                    hi = hi.as_long()
                if z3.is_expr(lo):
                    lo = z3.simplify(lo)
                    lo = lo.as_long()
                
                REGS[rd] = z3.simplify(z3.SignExt(24, z3.Extract(hi, lo, MEMORY.load(addr_round))))

            case mips.MIPS_INS_LBU:
                rd = operands[0]
                pc, rs = operands[1]
                addr = REGS[rs] + pc
                addr_round = addr & z3.BitVecVal(~0b11, 32)
                if z3.is_expr(addr_round):
                    addr_round = z3.simplify(addr_round)
                offset = addr & 0b11
                if z3.is_expr(offset):
                    offset = z3.simplify(offset)
                
                hi = 31 - 8 * offset
                lo = 24 - 8 * offset
                if z3.is_expr(hi):
                    hi = z3.simplify(hi)
                    hi = hi.as_long()
                if z3.is_expr(lo):
                    lo = z3.simplify(lo)
                    lo = lo.as_long()
                
                REGS[rd] = z3.simplify(z3.ZeroExt(24, z3.Extract(hi, lo, MEMORY.load(addr_round))))

            case mips.MIPS_INS_SW:
                rd = operands[0]
                pc, rs = operands[1]
                MEMORY.store(REGS[rs] + pc, REGS[rd])

            case mips.MIPS_INS_SH:
                rd = operands[0]
                pc, rs = operands[1]
                addr = REGS[rs] + pc
                addr_round = addr & ~0b11
                offset = addr & 0b11

                value = MEMORY.load(addr_round)
                hi = 31 - 8 * offset
                lo = 16 - 8 * offset
                mask = ~(((1 << 16) - 1) << lo)
                if z3.is_expr(mask):
                    mask = z3.simplify(mask)
                shift = (REGS[rd] & 0xFFFF) << lo

                MEMORY.store(addr_round, (value & z3.BitVecVal(mask, 32)) | shift)

            case mips.MIPS_INS_SB:
                rd = operands[0]
                pc, rs = operands[1]
                addr = REGS[rs] + pc
                addr_round = addr & ~0b11
                offset = addr & 0b11

                value = MEMORY.load(addr_round)
                hi = 31 - 8 * offset
                lo = 24 - 8 * offset
                mask = ~(((1 << 8) - 1) << lo)
                if z3.is_expr(mask):
                    mask = z3.simplify(mask)
                shift = (REGS[rd] & 0xFF) << lo

                MEMORY.store(addr_round, (value & z3.BitVecVal(mask, 32)) | shift)

            case mips.MIPS_INS_MFHI:
                rd = operands[0]
                REGS[rd] = REGS[mips.MIPS_REG_HI]

            case mips.MIPS_INS_MFLO:
                rd = operands[0]
                REGS[rd] = REGS[mips.MIPS_REG_LO]

            case mips.MIPS_INS_MOVE:
                rd, rs = operands
                REGS[rd] = REGS[rs]

            case mips.MIPS_INS_SLT:
                rd, rs, rt = operands
                if self.bool_proxy(REGS[rs] < REGS[rt]):
                    REGS[rd] = 1
                else:
                    REGS[rd] = 0

            case mips.MIPS_INS_SLTU:
                rd, rs, rt = operands
                if self.bool_proxy(z3.ULT(REGS[rs], REGS[rt])):
                    REGS[rd] = 1
                else:
                    REGS[rd] = 0

            case mips.MIPS_INS_JR:
                rs = operands[0]
                pc = REGS[rs]
                if isinstance(pc, int):
                    self.jump_to(pc)
                elif isinstance(pc, z3.BitVecNumRef):
                    self.jump_to(pc.as_long())
                else:
                    raise ValueError(f"{type(pc)} not supported")

            case mips.MIPS_INS_SYSCALL:
                syscall_num = REGS[mips.MIPS_REG_V0]
                handler = get_syscall_handler(syscall_num)
                if not handler:
                    raise ValueError(
                        f"syscall [{syscall_num}] not yet supported")
                handler(REGS, MEMORY)

            case mips.MIPS_INS_NOP:
                pass

            case mips.MIPS_INS_BEQ:
                rs, rt, pc = operands
                if self.bool_proxy(REGS[rs] == REGS[rt]):
                    self.jump_to(pc)
                else:
                    self.jump_to(insn.address + 4)
            case mips.MIPS_INS_BNE:
                rs, rt, pc = operands
                if self.bool_proxy(REGS[rs] != REGS[rt]):
                    self.jump_to(pc)
                else:
                    self.jump_to(insn.address + 4)
            case mips.MIPS_INS_BEQZ:
                rs, pc = operands
                if self.bool_proxy(REGS[rs] == 0):
                    self.jump_to(pc)
                else:
                    self.jump_to(insn.address + 4)
            case mips.MIPS_INS_BNEZ:
                rs, pc = operands
                if self.bool_proxy(REGS[rs] != 0):
                    self.jump_to(pc)
                else:
                    self.jump_to(insn.address + 4)
            case mips.MIPS_INS_BLEZ:
                rs, pc = operands
                if self.bool_proxy(REGS[rs] <= 0):
                    self.jump_to(pc)
                else:
                    self.jump_to(insn.address + 4)
            case mips.MIPS_INS_BLTZ:
                rs, pc = operands
                if self.bool_proxy(REGS[rs] < 0):
                    self.jump_to(pc)
                else:
                    self.jump_to(insn.address + 4)
            case mips.MIPS_INS_BGEZ:
                rs, pc = operands
                if self.bool_proxy(REGS[rs] >= 0):
                    self.jump_to(pc)
                else:
                    self.jump_to(insn.address + 4)
            case mips.MIPS_INS_BGTZ:
                rs, pc = operands
                if self.bool_proxy(REGS[rs] > 0):
                    self.jump_to(pc)
                else:
                    self.jump_to(insn.address + 4)

            # actually not I-type, but for convenience
            case mips.MIPS_INS_SLL:
                rd, rs, shamt = operands
                REGS[rd] = REGS[rs] << shamt

            case mips.MIPS_INS_SLLV:
                rd, rs, rt = operands
                REGS[rd] = REGS[rs] << REGS[rt]

            case mips.MIPS_INS_SRL:
                rd, rs, shamt = operands
                val = REGS[rs]
                if not z3.is_expr(val):
                    val = z3.BitVecVal(val, 32)
                REGS[rd] = z3.LShR(val, shamt)

            case mips.MIPS_INS_SRLV:
                rd, rs, rt = operands
                val = REGS[rs]
                if not z3.is_expr(val):
                    val = z3.BitVecVal(val, 32)
                REGS[rd] = z3.LShR(val, REGS[rt])

            case mips.MIPS_INS_ADDI:
                rd, rs, imm = operands
                REGS[rd] = REGS[rs] + imm
                self.check_overflow()

            case mips.MIPS_INS_ADDIU:
                rd, rs, imm = operands
                REGS[rd] = REGS[rs] + imm

            case mips.MIPS_INS_ANDI:
                rd, rs, imm = operands
                REGS[rd] = REGS[rs] & imm

            case mips.MIPS_INS_ORI:
                rd, rs, imm = operands
                REGS[rd] = REGS[rs] | imm

            case mips.MIPS_INS_LUI:
                rs, imm = operands
                REGS[rs] = imm << 16

            case mips.MIPS_INS_SLTI:
                rd, rs, imm = operands
                if self.bool_proxy(REGS[rs] < imm):
                    REGS[rd] = 1
                else:
                    REGS[rd] = 0

            case mips.MIPS_INS_SLTIU:
                rd, rs, imm = operands
                if self.bool_proxy(z3.ULT(REGS[rs], imm)):
                    REGS[rd] = 1
                else:
                    REGS[rd] = 0

            case mips.MIPS_INS_J:
                pc = operands[0]
                self.jump_to(pc)

            case mips.MIPS_INS_JAL:
                pc = insn.address
                REGS[mips.MIPS_REG_RA] = pc + 8

                pc = operands[0]
                self.jump_to(pc, True)

            case mips.MIPS_INS_BAL:
                pc = insn.address
                REGS[mips.MIPS_REG_RA] = pc + 8

                pc = operands[0]
                self.jump_to(pc, True)

            case mips.MIPS_INS_B:
                pc = operands[0]
                self.jump_to(pc)

            case mips.MIPS_INS_JALR:
                rs = operands[0]

                pc = insn.address
                REGS[mips.MIPS_REG_RA] = pc + 8
                # print(REGS[rs])
                target_address = REGS[rs].arg(1).as_long()
                # call __libc_start_main
                if self.global_table.get(target_address) != None and self.global_table.get(target_address) == "__libc_start_main":
                    REGS[mips.MIPS_REG_RA] = MAGIC_RETURN  # main return

                    # $a0 -> argc; $a1 -> argv -> stack; $a2 -> envp -> skip now...
                    if self.type == "run":
                        REGS[mips.MIPS_REG_A0] = z3.BitVec("$a0", 32)
                        REGS[mips.MIPS_REG_A1] = STACK_TOP - 4 * MAX_ARGC
                        REGS[mips.MIPS_REG_A2] = 0
                    elif self.type == "trace":
                        argc,  = self.args
                        argv = STACK_TOP - 4 * MAX_ARGC
                        envp = 0
                        REGS[mips.MIPS_REG_A0] = argc
                        REGS[mips.MIPS_REG_A1], REGS[mips.MIPS_REG_A2] = argv, 0

                    self.jump_to(self.main_address, False)
                # call dynamic library function
                elif self.global_table.get(target_address) != None:
                    if hasattr(libc, self.global_table.get(target_address)):
                        func_name = self.global_table.get(target_address)
                        func = getattr(
                            libc, func_name)
                        
                        func(REGS, MEMORY, self.type)

                        self.jump_to(REGS[mips.MIPS_REG_RA],
                                     False)  # is correct?
                else:
                    self.jump_to(REGS[rs], True)

            case _:
                raise NotImplementedError(f"not yet: {insn} {hex(insn.address)}")

    def jump_to(self, address: int, calling=False):
        # delay slot execute
        delay_pc = self.uc.reg_read(UC_MIPS_REG_PC)
        self.hook_instr(self.uc, delay_pc, 4, None)

        uc = self.uc
        REGS, MEMORY = self.regs, self.memory

        if calling:
            # TODO: check GOT
            pass
        if address == MAGIC_RETURN:
            REGS[mips.MIPS_REG_A0] = REGS[mips.MIPS_REG_V0]
            handle_sys_exit(REGS, MEMORY)

        uc.reg_write(UC_MIPS_REG_PC, address)

    def bool_proxy(self, term):
        if isinstance(term, bool):
            return term
        if z3.simplify(term).decl().kind() == z3.Z3_OP_TRUE:
            return True
        if z3.simplify(term).decl().kind() == z3.Z3_OP_FALSE:
            return False

        if self.type == "trace":
            raise ValueError(f"symbol while tracing: {term}")

        terms, conditions = self.terms, self.conditions

        if z3.simplify(term) not in conditions and z3.simplify(z3.Not(term)) not in conditions:
            s = z3.Solver()
            s.add(z3.And(*(conditions + [z3.simplify(term)])))
            true_cond = True if s.check() == z3.sat else False

            s = z3.Solver()
            s.add(z3.And(*(conditions + [z3.simplify(z3.Not(term))])))
            false_cond = True if s.check() == z3.sat else False

            if true_cond and not false_cond:
                return True
            if false_cond and not true_cond:
                return False

        if len(terms) > len(conditions):
            branch = terms[len(conditions)]
            conditions.append(
                z3.simplify(term) if branch else z3.simplify(z3.Not(term)))
            return branch

        if len(terms) >= 10:
            raise EmulatorStop("Depth exceeded")

        terms.append(True)
        conditions.append(z3.simplify(term))
        return True

    def get_lineno_by_address(self, addr):
        dwarf_info = self.elf.get_dwarf_info()
        for cu in dwarf_info.iter_CUs():
            line = 1
            for entry in dwarf_info.line_program_for_CU(cu).get_entries():
                if entry.state:
                    if addr > entry.state.address:
                        line = entry.state.line
                    else:
                        return line

    def symbolic(self, func_addr_start) -> list[z3.ModelRef]:
        self.type = "run"

        self.terms = []
        uc = self.uc

        models = []
        while True:
            self.conditions = []

            self.regs = Registers()
            self.memory = deepcopy(self.memory_init)
            self.regs[mips.MIPS_REG_SP] = STACK_TOP - 4 * MAX_ARGC

            uc.reg_write(UC_MIPS_REG_SP, STACK_TOP - 4 * MAX_ARGC)
            uc.reg_write(UC_MIPS_REG_PC, func_addr_start)
            try:
                uc.emu_start(func_addr_start, 0)
            except EmulatorStop as e:
                print("Emu stopped:", e)

            s = z3.Solver()
            s.add(z3.And(*self.conditions))
            if s.check() == z3.sat:
                models.append(s.model())

            while len(self.terms) > 0 and not self.terms[-1]:
                self.terms.pop()
            if len(self.terms) == 0:
                break
            self.terms[-1] = False

        return models

    def run_with_val(self, func_addr_start, regs, mem):
        uc = self.uc

        self.regs = Registers()
        self.args = []
        for reg_id, value in regs:
            self.regs[reg_id] = value
            if reg_id in (mips.MIPS_REG_A0,):
                self.args.append(value)

        self.memory = deepcopy(self.memory_init)
        for addr in range(align_down(STACK_TOP - STACK_SIZE), STACK_TOP - 4 * MAX_ARGC, 4):
            self.memory.store(addr, mem[1])

        for addr in range(MAGIC_ARG, MAGIC_ARG + MAX_ARGC * MAX_ARG_LEN, 4):
            self.memory.store(addr, mem[1])

        for addr, val in mem[0].items():
            self.memory.store(addr, val)

        self.regs[mips.MIPS_REG_SP] = STACK_TOP - 4 * MAX_ARGC
        uc.reg_write(UC_MIPS_REG_SP, STACK_TOP - 4 * MAX_ARGC)
        uc.reg_write(UC_MIPS_REG_PC, func_addr_start)
        try:
            uc.emu_start(func_addr_start, 0)
        except EmulatorStop as e:
            print("Emu stopped:", e)

    def trace(self, func_addr_start, models: list[z3.ModelRef]) -> set[int]:
        self.type = "trace"
        self.coverage = set()
        # TODO: args, coverage, deadcode

        for model in models:
            print("Running with Model:", model)
            regs = list(Registers.evaluate(model))
            mem = extract_array_store(model, Memory.evaluate(model))
            self.run_with_val(func_addr_start, regs, mem)

        return self.coverage

    def show_coverage(self, executed_addr: set[int]):
        for func in self.functions:
            instr_addrs = list(range(func['start'], func['end'], 4))
            exec_in_func = set(instr_addrs) & executed_addr
            if exec_in_func:
                func['executed'] = True

            func['dead'] = [addr for addr in instr_addrs if addr not in exec_in_func]

        total = len(self.functions)
        executed_funcs = sum(1 for f in self.functions if f['executed'])
        coverage_pct = executed_funcs / total * 100 if total else 0

        md = self.md
        uc = self.uc

        print(f"Total functions count: {total}")
        print(f"Executed functions count: {executed_funcs}")
        print(f"Function coverage: {coverage_pct:.2f}%")
        print("\nFunction detail:")
        for f in self.functions:
            status = ":)" if f['executed'] else ":("
            dead_count = len(f['dead'])
            size = (f['end'] - f['start']) // 4
            cov = (size - dead_count) / size * 100 if size else 0
            print(f"\n[{status}] {f['name']}")
            print(f"  Address range: [0x{f['start']:08x} - 0x{f['end']:08x})")
            print(f"  Coverage: {cov:.1f}% ({size-dead_count}/{size} instr.)")
            print(f"  Dead instructions:")
            if dead_count:
                if f['executed']:
                    for idx, addr in enumerate(f['dead']):
                        insn_bytes = uc.mem_read(addr, 4)
                        for insn in md.disasm(insn_bytes, addr):
                            print(
                                f"    0x{addr:08x} {insn.mnemonic} {insn.op_str}")
                        if idx + 1 < len(f['dead']):
                            if f['dead'][idx + 1] - addr > 4:
                                print("    =====================================")
                    if self.debug:
                        print(f"  Dead line Number:")
                        lineno = []
                        for addr in f['dead']:
                            lineno.append(self.get_lineno_by_address(addr))
                        lineno = list(set(lineno))  # To delete duplicated element
                        if lineno:
                            print("  ", ", ".join([str(i) for i in lineno]))
                else:
                    print("    this function has never been executed")
            else:
                print("    No dead instructions")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description='Generate coverage report using symbolic execution.')
    parser.add_argument('-t', '--target', required=True,
                        help="the target file to symbolically execute")
    parser.add_argument('-v', '--verbose',
                        action="store_true", help="debug print")
    args = parser.parse_args()

    target = args.target
    verbose = args.verbose

    emul = Mips32Emulator(target, verbose)
    print("[symbolic]")
    models = emul.symbolic(emul.entry)
    print()

    print("[trace]")
    coverage = emul.trace(emul.entry, models)
    print()

    print("[coverage]")
    emul.show_coverage(coverage)
    print()

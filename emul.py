import sys
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
from elftools.elf.sections import SymbolTableSection, Section
from elftools.elf.dynamic import DynamicSection
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

from state import Memory, Registers
from symlibc import Libc as libc 
from syscall import SYSCALL_HANDLERS
PAGE_SIZE = 0x1000


def align_down(addr, align=PAGE_SIZE):
    return addr & ~(align - 1)


def align_up(addr, align=PAGE_SIZE):
    return (addr + align - 1) & ~(align - 1)




MEMORY = Memory()
REGS = Registers()



def classify(insn: CsInsn):
    # J-type (jump / jal)
    if insn.id in (mips.MIPS_INS_J, mips.MIPS_INS_JAL, mips.MIPS_INS_BAL, mips.MIPS_INS_JALR):
        return "J"
    # I-type (imm)
    for operand in insn.operands:
        if operand.type == CS_OP_IMM:
            return "I"
    # R-type (else)
    return "R"


conditions = []
terms = []
global_table = {}
main_address = None

def bool_proxy(term):
    if isinstance(term, bool):
        return term
    global terms, conditions
    s = z3.Solver()
    s.add(z3.And(*(conditions + [term])))
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
            term if branch else z3.simplify(z3.Not(term)))
        return branch

    if len(terms) >= 10:
        raise DepthException()

    terms.append(True)
    conditions.append(term)
    return True


class DepthException(Exception):
    pass


def handle_overflow():
    # not yet
    pass


def handle_Rtype(insn: CsInsn):
    operands = list(parse_operand(insn))
    match insn.id:
        case mips.MIPS_INS_ADD:
            rd, rs, rt = operands
            REGS[rd] = REGS[rs] + REGS[rt]
            handle_overflow()

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

        case mips.MIPS_INS_SLL:
            rd, rs, shamt = operands
            REGS[rd] = REGS[rs] << shamt

        case mips.MIPS_INS_SRL:
            rd, rs, shamt = operands
            REGS[rd] = z3.LShR(REGS[rs], shamt)

        case mips.MIPS_INS_LW:
            rd = operands[0]
            pc, rs = operands[1]
            REGS[rd] = MEMORY.load(REGS[rs] + pc)

        case mips.MIPS_INS_SW:
            rd = operands[0]
            pc, rs = operands[1]
            MEMORY.store(REGS[rs] + pc, REGS[rd])

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
            if bool_proxy(REGS[rs] < REGS[rt]):
                REGS[rd] = 1
            else:
                REGS[rd] = 0

        case mips.MIPS_INS_JR:
            rs = operands[0]
            pc = REGS[rs]
            if isinstance(pc, int):
                jump_to(pc)
            else:
                raise ValueError("not supported")

        case mips.MIPS_INS_SYSCALL:
            syscall_num = REGS[mips.MIPS_REG_V0]
            handler = SYSCALL_HANDLERS.get(syscall_num)
            if not handler:
                raise ValueError(
                    f"syscall [{syscall_num}] not yet supported")
            handler(REGS, MEMORY) 
        
        case mips.MIPS_INS_NOP:
            pass
        
        case _:
            raise NotImplementedError(f"not yet: {insn}")


def handle_Itype(insn: CsInsn):
    operands = list(parse_operand(insn))
    match insn.id:
        case mips.MIPS_INS_BEQ:
            rs, rt, pc = operands
            if bool_proxy(REGS[rs] == REGS[rt]):
                jump_to(pc)
            else:
                jump_to(insn.address + 4)
        case mips.MIPS_INS_BNE:
            rs, rt, pc = operands
            if bool_proxy(REGS[rs] != REGS[rt]):
                jump_to(pc)
            else:
                jump_to(insn.address + 4)

        case mips.MIPS_INS_ADDI:
            rd, rs, imm = operands
            REGS[rd] = REGS[rs] + imm
            handle_overflow()

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
            if bool_proxy(REGS[rs] < imm):
                REGS[rd] = 1
            else:
                REGS[rd] = 0
        case _:
            raise NotImplementedError(f"not yet: {insn}")

def handle_Jtype(insn: CsInsn):
    operands = list(parse_operand(insn))
    match insn.id:
        case mips.MIPS_INS_J:
            pc = operands[0]
            jump_to(pc)

        case mips.MIPS_INS_JAL:
            pc = insn.address
            REGS[mips.MIPS_REG_RA] = pc + 4

            pc = operands[0]
            jump_to(pc, True)

        case mips.MIPS_INS_BAL:
            pc = insn.address
            REGS[mips.MIPS_REG_RA] = pc +4
            
            pc = operands[0]
            jump_to(pc, True)

        case mips.MIPS_INS_JALR:
            rs = operands[0]

            pc = insn.address
            REGS[mips.MIPS_REG_RA] = pc + 4
            # print(REGS[rs])
            target_address = REGS[rs].arg(1).as_long()
            if global_table.get(target_address) != None and global_table.get(target_address) == "__libc_start_main": # call __libc_start_main
                jump_to(main_address, False)
            elif global_table.get(target_address) != None: # call dynamic library function
                if hasattr(libc, global_table.get(target_address)):
                    func = getattr(libc, global_table.get(target_address))
                    func(REGS, MEMORY)
                    jump_to(REGS[mips.MIPS_REG_RA], False) # is correct?
            else:
                jump_to(REGS[rs], True)

        case _:
            raise NotImplementedError(f"not yet: {insn}")

def jump_to(address: int, calling = False):
    if calling:
        # TODO: check GOT
        pass
    uc.reg_write(UC_MIPS_REG_PC, address)


md = Cs(CS_ARCH_MIPS, CS_MODE_MIPS32 | CS_MODE_BIG_ENDIAN)
md.detail = True


def hook_instr(uc: Uc, address: int, size: int, user_data):
    insn_bytes = uc.mem_read(address, size)
    for insn in md.disasm(insn_bytes, address):
        print(insn)
        match classify(insn):
            case "R":
                handle_Rtype(insn)
            case "I":
                handle_Itype(insn)
            case "J":
                handle_Jtype(insn)


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

def dlloader(elffile, pointer_size):
    external_functions = {}
    dt_pltgot_addr = None
    dt_mips_local_gotno = None
    dt_mips_gotsym = None
    dt_mips_symtabno = None

    dynamic_section = elffile.get_section_by_name('.dynamic')
    if not dynamic_section or not isinstance(dynamic_section, DynamicSection):
        return external_functions

    for tag in dynamic_section.iter_tags():
        if tag.entry.d_tag == 'DT_PLTGOT':
            dt_pltgot_addr = tag.entry.d_val
        elif tag.entry.d_tag == 'DT_MIPS_LOCAL_GOTNO':
            dt_mips_local_gotno = tag.entry.d_val
        elif tag.entry.d_tag == 'DT_MIPS_GOTSYM':
            dt_mips_gotsym = tag.entry.d_val
        elif tag.entry.d_tag == 'DT_MIPS_SYMTABNO':
            dt_mips_symtabno = tag.entry.d_val
    
    if not all(val is not None for val in [dt_pltgot_addr, dt_mips_local_gotno, dt_mips_gotsym, dt_mips_symtabno]):
        return external_functions

    dynsym_section = elffile.get_section_by_name('.dynsym')
    if not dynsym_section or not isinstance(dynsym_section, SymbolTableSection):
        return external_functions

    global_got_entry_addr = dt_pltgot_addr + (dt_mips_local_gotno * pointer_size)
    global_got_entries = dt_mips_symtabno - dt_mips_gotsym

    if global_got_entries < 0:
        return external_functions

    for i in range(global_got_entries):
        current_dynsym_idx = dt_mips_gotsym + i
        current_got_entry_addr = global_got_entry_addr + (i * pointer_size)
        symbol = dynsym_section.get_symbol(current_dynsym_idx)
        if symbol['st_info']['type'] == 'STT_FUNC' and symbol['st_shndx'] == 'SHN_UNDEF' and symbol.name:
            external_functions[current_got_entry_addr] = symbol.name
    return external_functions

def get_symbol_table(elffile) -> dict[int, str]:
    got_function_map = {}
    dt_pltgot_addr = None
    pointer_size = elffile.elfclass // 8
    external_functions = dlloader(elffile, pointer_size)
    
    if not external_functions:
        print("Not Found external functions")

    dynamic_section = elffile.get_section_by_name('.dynamic')
    if dynamic_section and isinstance(dynamic_section, DynamicSection):
            for tag in dynamic_section.iter_tags():
                if tag.entry.d_tag == 'DT_PLTGOT':
                    dt_pltgot_addr = tag.entry.d_val
                    break

    got_section_to_read = None
    if dt_pltgot_addr is not None:
        for section in elffile.iter_sections():
            if section.header['sh_addr'] <= dt_pltgot_addr < section.header['sh_addr'] + section.header['sh_size']:
                got_section_to_read = section
    
    if not got_section_to_read:
        got_section_to_read = elffile.get_section_by_name('.got')
        if not got_section_to_read:
            got_section_to_read = elffile.get_section_by_name('.got.plt')


    if got_section_to_read and isinstance(got_section_to_read, Section) and \
        got_section_to_read.header['sh_type'] != 'SHT_NOBITS':
        section_data = got_section_to_read.data()
        num_entries = len(section_data) // pointer_size

        for i in range(num_entries):
            offset_in_section = i * pointer_size
            entry_bytes = section_data[offset_in_section : offset_in_section + pointer_size]
            
            if len(entry_bytes) == pointer_size:
                entry_address = got_section_to_read.header['sh_addr'] + offset_in_section
                
                func_name = external_functions.get(entry_address, None)
                got_function_map[entry_address] = func_name
            else:
                continue
    return got_function_map

def map_elf(uc: Uc, path: str):
    global global_table, main_address
    with open(path, "rb") as f:
        elf = ELFFile(f)

        global_table = get_symbol_table(elf)
        found_main = False
        for symbol in elf.get_section_by_name('.symtab').iter_symbols():
            if symbol.name == 'main':
                if symbol['st_info']['type'] == 'STT_FUNC':
                    main_address = symbol['st_value']
                    found_main = True
                    break
        if not found_main:
            print("Is This stripped binary?")
            


        # sp todo

        for seg in elf.iter_segments():
            if seg["p_type"] != "PT_LOAD":
                continue

            vaddr = seg["p_vaddr"]
            memsz = seg["p_memsz"]
            filesz = seg["p_filesz"]
            data = seg.data()

            # 페이지 경계로 맞춰 매핑
            base = align_down(vaddr)
            top = align_up(vaddr + memsz)
            size = top - base

            # 읽기/쓰기/실행 권한 모두 설정
            uc.mem_map(base, size, UC_PROT_READ | UC_PROT_WRITE | UC_PROT_EXEC)

            # 파일에 있는 부분만 써주고, 나머지는 0으로 남겨둠 (.bss 영역 대비)
            offset_in_page = vaddr - base
            uc.mem_write(vaddr, data)
            if memsz > filesz:
                uc.mem_write(vaddr + filesz, b"\x00" * (memsz - filesz))

    return elf.header["e_entry"]


uc = Uc(UC_ARCH_MIPS, UC_MODE_MIPS32 | UC_MODE_BIG_ENDIAN)

entry = map_elf(uc, sys.argv[1])

STACK_TOP = 0x7fff0000
STACK_SIZE = PAGE_SIZE
uc.mem_map(align_down(STACK_TOP - STACK_SIZE),
           STACK_SIZE, UC_PROT_READ | UC_PROT_WRITE)
uc.reg_write(UC_MIPS_REG_SP, STACK_TOP - 4)

uc.reg_write(UC_MIPS_REG_PC, entry)

uc.hook_add(UC_HOOK_CODE, hook_instr)


def run():
    global terms, conditions
    terms = []
    models = []
    while True:
        conditions = []
        try:
            uc.emu_start(entry, 0)
        except Exception as e:
            print("Emu stopped:", e)

        s = z3.Solver()
        s.add(z3.And(*conditions))
        s.check()
        models.append(s.model())

        while len(terms) > 0 and not terms[-1]:
            terms.pop()
        if len(terms) == 0:
            break
        terms[-1] = False

    return models


models = run()
for model in models:
    print(model)

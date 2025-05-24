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

from register import Registers


PAGE_SIZE = 0x1000


def align_down(addr, align=PAGE_SIZE):
    return addr & ~(align - 1)


def align_up(addr, align=PAGE_SIZE):
    return (addr + align - 1) & ~(align - 1)


Addr = z3.BitVecSort(32)
Value = z3.BitVecSort(32)

MEMORY = z3.Array("MEMORY", Addr, Value)
REGS = Registers()


def load(addr):
    return z3.Select(MEMORY, addr)


def store(addr, value):
    MEMORY = z3.Store(MEMORY, addr, value)


def classify(insn: CsInsn):
    # J-type (jump / jal)
    if insn.id in (mips.MIPS_INS_J, mips.MIPS_INS_JAL):
        return "J"
    # I-type (imm)
    for operand in insn.operands:
        if operand.type == CS_OP_IMM:
            return "I"
    # R-type (else)
    return "R"


conditions = []
terms = []


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
            REGS[rd] = load(REGS[rs] + pc)

        case mips.MIPS_INS_SW:
            rd = operands[0]
            pc, rs = operands[1]
            store(REGS[rs] + pc, REGS[rd])

        case mips.MIPS_INS_MFHI:
            rd = operands[0]
            REGS[rd] = REGS[mips.MIPS_REG_HI]

        case mips.MIPS_INS_MFLO:
            rd = operands[0]
            REGS[rd] = REGS[mips.MIPS_REG_LO]

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
            raise ValueError(
                f"syscall [{REGS[mips.MIPS_REG_V0]}] not yet supported")


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
            jump_to(pc)


def jump_to(address: int):
    uc.reg_write(UC_MIPS_REG_PC, address)


md = Cs(CS_ARCH_MIPS, CS_MODE_MIPS32 | CS_MODE_BIG_ENDIAN)
md.detail = True


def hook_instr(uc: Uc, address: int, size: int, user_data):
    insn_bytes = uc.mem_read(address, size)
    for insn in md.disasm(insn_bytes, address):
        match classify(insn):
            case "R":
                handle_Rtype(insn)
            case "I":
                handle_Itype(insn)
            case "R":
                handle_Rtype(insn)


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


def map_elf(uc: Uc, path: str):
    with open(path, "rb") as f:
        elf = ELFFile(f)
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
uc.reg_write(UC_MIPS_REG_SP, STACK_TOP)

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

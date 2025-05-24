from unicorn import UC_HOOK_INTR, Uc, UC_ARCH_MIPS, UC_MODE_MIPS32, UC_MODE_BIG_ENDIAN, UC_PROT_READ, UC_PROT_WRITE, UC_PROT_EXEC, UC_HOOK_CODE
from unicorn.mips_const import UC_MIPS_REG_SP, UC_MIPS_REG_PC
from elftools.elf.elffile import ELFFile
from capstone import CS_OP_IMM, CS_OP_MEM, CS_OP_REG, Cs, CS_ARCH_MIPS, CS_MODE_MIPS32, CS_MODE_BIG_ENDIAN, CsInsn
import capstone.mips_const as mips


PAGE_SIZE = 0x1000


def align_down(addr, align=PAGE_SIZE):
    return addr & ~(align - 1)


def align_up(addr, align=PAGE_SIZE):
    return (addr + align - 1) & ~(align - 1)


def map_elf(uc, path):
    with open(path, 'rb') as f:
        elf = ELFFile(f)
        for seg in elf.iter_segments():
            if seg['p_type'] != 'PT_LOAD':
                continue

            vaddr = seg['p_vaddr']
            memsz = seg['p_memsz']
            filesz = seg['p_filesz']
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
                uc.mem_write(vaddr + filesz, b'\x00' * (memsz - filesz))

    return elf.header['e_entry']


# Unicorn 초기화
uc = Uc(UC_ARCH_MIPS, UC_MODE_MIPS32 | UC_MODE_BIG_ENDIAN)

# ELF 매핑 및 엔트리 얻기
entry = map_elf(uc, "test")

# 스택 영역 매핑 (1페이지)
STACK_TOP = 0x7fff0000
STACK_SIZE = PAGE_SIZE
uc.mem_map(align_down(STACK_TOP - STACK_SIZE),
           STACK_SIZE, UC_PROT_READ | UC_PROT_WRITE)
uc.reg_write(UC_MIPS_REG_SP, STACK_TOP)

uc.reg_write(UC_MIPS_REG_PC, entry)

md = Cs(CS_ARCH_MIPS, CS_MODE_MIPS32 | CS_MODE_BIG_ENDIAN)
md.detail = True

def classify(insn: CsInsn):
    # J-type (jump / jal)
    if insn.id in (mips.MIPS_INS_J, mips.MIPS_INS_JAL):
        return "J"
    # I-type (즉시값 있는 경우)
    for operand in insn.operands:
        if operand.type == CS_OP_IMM:
            return "I"
    # R-type (그 외)
    return "R"

def handle_Rtype(insn: CsInsn):
    match insn.id:
        case mips.MIPS_INS_ADD:
            pass
        case mips.MIPS_INS_SUB:
            pass
        case mips.MIPS_INS_ADDU:
            pass
        case mips.MIPS_INS_SUBU:
            pass
        case mips.MIPS_INS_MUL:
            pass
        case mips.MIPS_INS_MULT:
            pass
        case mips.MIPS_INS_DIV:
            pass
        case mips.MIPS_INS_AND:
            pass
        case mips.MIPS_INS_OR:
            pass
        case mips.MIPS_INS_SLL:
            pass
        case mips.MIPS_INS_SRL:
            pass
        case mips.MIPS_INS_LW:
            pass
        case mips.MIPS_INS_SW:
            pass
        case mips.MIPS_INS_MFLO:
            pass
        case mips.MIPS_INS_BEQ:
            pass
        case mips.MIPS_INS_BNE:
            pass
        case mips.MIPS_INS_SLT:
            pass
        case mips.MIPS_INS_JR:
            pass
        case mips.MIPS_INS_SYSCALL:
            pass

def handle_Itype(insn: CsInsn):
    match insn.id:
        case mips.MIPS_INS_ADDI:
            pass
        case mips.MIPS_INS_ADDIU:
            pass
        case mips.MIPS_INS_ANDI:
            pass
        case mips.MIPS_INS_ORI:
            pass
        case mips.MIPS_INS_LUI:
            pass
        case mips.MIPS_INS_MFHI:
            pass
        case mips.MIPS_INS_SLTI:
            pass
        
def handle_Jtype(insn: CsInsn):
    match insn.id:
        case mips.MIPS_INS_J:
            pass
        case mips.MIPS_INS_JAL:
            pass

def hook_instr(uc: Uc, address: int, size: int, user_data):
    # print(type(uc), type(address), type(size), type(user_data))
    insn_bytes = uc.mem_read(address, size)
    for insn in md.disasm(insn_bytes, address):
        parse_operand(insn)
        match classify(insn):
            case "R":
                handle_Rtype(insn)
            case "I":
                handle_Itype(insn)
            case "R":
                handle_Rtype(insn)

     
        # print()

def parse_operand(insn: CsInsn):
    for op in insn.operands:
        if op.type == CS_OP_REG:
            print("   - reg     :", md.reg_name(op.reg))
        elif op.type == CS_OP_IMM:
            print("   - imm     :", hex(op.imm))
        elif op.type == CS_OP_MEM:
            # mem.base, mem.index, mem.disp
            mem = op.mem
            base = md.reg_name(mem.base)
            disp = mem.disp
            print("   - mem     :", f"offset={hex(disp)}  base={base}")
        else:
            raise ValueError("noo")
        
uc.hook_add(UC_HOOK_CODE, hook_instr)

# def hook_intr(uc, intno, user_data):
#     print(f"Interrupt! intno = {intno}")

# uc.hook_add(UC_HOOK_INTR, hook_intr)

try:
    uc.emu_start(entry, 0)
except Exception as e:
    print("Emu stopped:", e)

# print("Covered instructions:", sorted(covered))

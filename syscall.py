from z3 import *
import capstone.mips_const as mips
from state import Memory, Registers

SYSCALL_EXIT = 4001

def handle_sys_exit(regs: Registers, mem: Memory):
    status_code = regs[mips.MIPS_REG_A0]
    raise SystemExit(f"Exit with {status_code} by syscall")

SYSCALL_HANDLERS = {
    SYSCALL_EXIT: handle_sys_exit
}
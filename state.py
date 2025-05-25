import capstone.mips_const as mips
import z3

REG_NAMES = [
    "zero", "at", "v0", "v1", "a0", "a1", "a2", "a3",
    "t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7",
    "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7",
    "t8", "t9", "k0", "k1", "gp", "sp", "fp", "ra"
]


class Registers:
    def __init__(self):
        # $0 -> 2번... 2씩 밀려 있음
        self._regs = {
            i+2: z3.BitVec(f"${REG_NAMES[i]}", 32) for i in range(32)}
        self._regs[mips.MIPS_REG_ZERO] = 0
        self._regs[mips.MIPS_REG_HI] = z3.BitVec("$hi", 32)
        self._regs[mips.MIPS_REG_LO] = z3.BitVec("$lo", 32)

    def __getitem__(self, idx: int):
        if idx == mips.MIPS_REG_ZERO:
            return 0
        reg = self._regs.get(idx)
        if reg == None:
            raise IndexError(f"REG INDEX [{idx}] Not Supported")
        return reg

    def __setitem__(self, idx: int, value):
        if idx == mips.MIPS_REG_ZERO:
            self._regs[idx] = 0
            return
        reg = self._regs.get(idx)
        if reg == None:
            raise IndexError(f"REG INDEX [{idx}] Not Supported")
        self._regs[idx] = value

    def copy(self):
        new_regs = Registers()
        new_regs._regs = list(self._regs)
        return new_regs


AddrSort = z3.BitVecSort(32)
ValueSort = z3.BitVecSort(32)


class Memory:
    def __init__(self):
        self._mem = z3.Array("MEMORY", AddrSort, ValueSort)

    def load(self, addr):
        value = z3.Select(self._mem, addr)
        if z3.is_expr(value):
            return z3.simplify(value)
        return value

    def store(self, addr, value):
        if z3.is_expr(value):
            value = z3.simplify(value)
        self._mem = z3.Store(self._mem, addr, value)

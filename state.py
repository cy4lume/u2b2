import capstone.mips_const as mips
import z3


class Registers:
    def __init__(self):
        self._regs = [z3.BitVec(f"REG{i}", 32) for i in range(256)]
        self._regs[mips.MIPS_REG_ZERO]

    def __getitem__(self, idx: int):
        if idx == mips.MIPS_REG_ZERO:
            return 0
        return self._regs[idx]

    def __setitem__(self, idx: int, value):
        if idx == mips.MIPS_REG_ZERO:
            self._regs[idx] = 0
            return
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
        return z3.Select(self._mem, addr)

    def store(self, addr, value):
        self._mem = z3.Store(self._mem, addr, value)

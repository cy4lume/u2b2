# u2b2
CS453 project: Unreachable Bytecode BUster for MIPS32

Build MIPS32 Binary:
`mips-linux-gnu-as -EB -march=mips32 exploit.s -o exploit.o`
`mips-linux-gnu-ld exploit.o -o exploit.elf -e exploit`
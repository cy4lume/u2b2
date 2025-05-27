# u2b2
CS453 project: Unreachable Bytecode BUster for MIPS32

Build MIPS32 Binary:
`mips-linux-gnu-as -EB -march=mips32 exploit.s -o exploit.o`
`mips-linux-gnu-ld exploit.o -o exploit.elf -e exploit`

or

`mips-linux-gnu-gcc -march=mips32 -mabi=32 -EB test_func.c -o test_func.elf`

## Compatibility
Supported Architecture  : 32-bit, MIPS (MIPS32)

Supported Platform      : Linux

Supported Format        : ELF (dynamically linked)

## Usage
```
python3 emul.py -t <TARGET_ELF> [-v]
    -t, --target        the target file to symbolically execute
    -v, --verbose       debug print
```
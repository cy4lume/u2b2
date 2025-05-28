from elftools.elf.sections import SymbolTableSection, Section
from elftools.elf.dynamic import DynamicSection
import ctypes.util
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
import os


PAGE_SIZE = 0x1000
LIBC_BASE = 0x00000000

def align_down(addr, align=PAGE_SIZE):
    return addr & ~(align - 1)


def align_up(addr, align=PAGE_SIZE):
    return (addr + align - 1) & ~(align - 1)


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

    global_got_entry_addr = dt_pltgot_addr + \
        (dt_mips_local_gotno * pointer_size)
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
            entry_bytes = section_data[offset_in_section:
                                       offset_in_section + pointer_size]

            if len(entry_bytes) == pointer_size:
                entry_address = got_section_to_read.header['sh_addr'] + \
                    offset_in_section

                func_name = external_functions.get(entry_address, None)
                got_function_map[entry_address] = func_name
            else:
                continue
    return got_function_map

class LibcSym:
    def __init__(self, uc: Uc, path):
        libc_path = os.path.join(path, "libc.so.6")

        f = open(libc_path, "rb")
        libc = ELFFile(f)

        dynsym = libc.get_section_by_name(".dynsym")
        self.dynsym  = { sym.name: sym['st_value']
                   for sym in dynsym.iter_symbols() if sym.name }

        for seg in libc.iter_segments():
            if seg.header.p_type != "PT_LOAD":
                continue

            vaddr = seg.header.p_vaddr
            memsz = seg.header.p_memsz
            filesz = seg.header.p_filesz
            data = seg.data()

            base = align_down(vaddr + LIBC_BASE)
            top = align_up(vaddr + memsz + LIBC_BASE)
            size = top - base

            uc.mem_map(base, size,
                        UC_PROT_READ | UC_PROT_WRITE | UC_PROT_EXEC)
        
            uc.mem_write(vaddr + LIBC_BASE, data)

            if memsz > filesz:
                uc.mem_write(vaddr + LIBC_BASE + filesz,
                            b"\x00" * (memsz - filesz))

    def get(self, fn: str)->int:
        # get libc function's vma
        rva = self.dynsym.get(fn)

        if not rva:
            raise KeyError(f"{fn} is not an libc symbol")
        
        return LIBC_BASE + rva

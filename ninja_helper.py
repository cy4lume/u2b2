from binaryninja import *
from binaryninjaui import UIContext

def get_got():
    ctx = UIContext.activeContext()
    if ctx is None:
        return None
    view = ctx.getCurrentView()
    if view is None:
        return None
    bv = view.getData()
    load_functions = {}
    got_section = bv.get_section_by_name(".got")
    if got_section:
        for address in range(got_section.start, got_section.end, 0x4):
            try:
                if bv.get_symbol_at(address).name:
                    func_name = bv.get_symbol_at(address).name
                    load_functions[address] = func_name
            except:
                continue
        return load_functions
from binaryninja import *

def get_got(bv: BinaryView):
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
            func_name = bv.get_symbol_at(address).name
            load_functions[address] = func_name
        return load_functions
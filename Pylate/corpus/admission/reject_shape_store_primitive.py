"""`shape-store`: an attribute store on a value no class layout covers.

Split out of `defects/soundness_heap_dispatch.py`, which the analysis must keep
admitting so its other findings stay covered. `int` has no `extra` field and no
class declares one, so the composite the lowering derives has nowhere to put it.
"""


def primitive_attribute_store(value: int) -> None:
    value.extra = 1

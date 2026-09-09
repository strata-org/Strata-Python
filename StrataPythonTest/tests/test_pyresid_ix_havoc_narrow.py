# Interaction: isinstance narrowing on a heap path must not survive an
# opaque call that can reach the object (set.intersection_update is
# known-but-unmodeled: receiver and arguments havocked, obligation
# emitted, and h.val goes back to its declared type).
class Holder:
    val: int

    def __init__(self, v: int):
        self.val = v


def poke(h, bag: set) -> int:
    if isinstance(h.val, int):
        bag.intersection_update({h})
        return h.val
    return 0


h = Holder(3)
r = poke(h, {h})

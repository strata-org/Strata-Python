# A sibling nested function has its OWN local `x`, a different binding from the
# enclosing `x` that `reads_x` captures. Forwarding the capture by name at the
# call in `other` would pass `other`'s `x` (99), not the captured enclosing `x`,
# so the call must be rejected rather than silently lowered to the wrong binding.
def outer(x: int) -> int:
    def reads_x() -> int:
        return x

    def other() -> int:
        x: int = 99
        return reads_x()

    return other()


outer(1)

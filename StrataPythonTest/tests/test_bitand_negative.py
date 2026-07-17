# Regression test for the non-negative-operand guard in intBandFunc.
#
# `int_band`'s concreteEval folds only when both operands are >= 0
# (using `Nat.land`, which agrees with Python only on non-negatives).
# Any negative operand returns `.none`, leaving the call symbolic — the
# `.expected` file below pins that graceful degradation.
#
# Why compare against the concrete literal `0` and not against the same
# expression on both sides: `assert z == -12 & 10` would pass trivially
# because both sides reduce to the same symbolic term `int_band(-12, 10)`,
# so `PEq` collapses via structural equality without exercising the guard.
# Comparing against `0` forces the assertion to stay symbolic, which is
# exactly the behavior we want to lock in.
#
# Without this pin, a future two's-complement fold with an off-by-one bug
# could return the wrong concrete value (e.g. `4` instead of `0`) and no
# other test would catch it — the three positive-operand bit tests (and
# every test in the langref corpus's `binary_bitwise` section) use
# non-negative literals only.
def test():
    x: int = -12
    y: int = 10
    z: int = x & y
    assert z == 0

test()

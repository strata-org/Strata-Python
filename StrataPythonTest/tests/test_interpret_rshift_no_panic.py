# Regression test for the shift-count guard in intRshiftFunc.
#
# `>>` lowers to `int_rshift(x, n)`, which the factory folds when
# `0 ≤ n ≤ maxPowExponent`. Without a guard, Lean's `Nat.pow` (called
# internally via `2 ^ nv.toNat`) panics for `n` above `UInt32.max`
# ("INTERNAL PANIC: Nat.pow exponent is too big", exit 1 — uncatchable at
# Lean level, unreachable via --fuel or Python try/except). The guard
# returns `.none` from `concreteEval` when the shift count is out of
# range, so the assertion stays symbolic instead.
#
# Companion to test_interpret_pow_no_panic.py, which covers `**` (and
# transitively `<<`, which routes through intPowFunc). `>>` uses
# intRshiftFunc's separate guard and needs its own case.
def test_rshift_no_panic():
    # 4_294_967_296 == 2**32 == UInt32.max + 1. Guard returns .none → symbolic.
    y: int = 1024 >> 4294967296
    assert y == 0


if __name__ == "__main__":
    test_rshift_no_panic()

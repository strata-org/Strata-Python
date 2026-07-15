# Regression test for the exponent guards in intPowFunc / intRshiftFunc
#
# Before the guards, `pyInterpret` folded `2 ** 4_294_967_296` etc. through
# Lean's `Nat.pow`, which panics for exponents above `UInt32.max`
# ("INTERNAL PANIC: Nat.pow exponent is too big", exit 1 — uncatchable at
# Lean level, unreachable via --fuel or Python try/except). The guards
# return `.none` from `concreteEval` when the exponent is out of range, so
# the assertion stays symbolic instead.
#
# The test uses assertions that CPython would *fail* (2**BIG is a huge
# positive number, not zero), so the .expected file below pins the
# "condition did not reduce to bool" outcome — i.e. the interpreter
# neither panics nor mis-folds; it stays symbolic exactly as intended.
def test_pow_no_panic():
    # 4_294_967_296 == 2**32 == UInt32.max + 1. Exponents at or above this
    # would abort Lean via Nat.pow. `intPowFunc`'s guard returns .none →
    # symbolic. `<<` routes through intPowFunc so it's transitively covered
    # by this case; `>>` has its own guard tested in test_rshift_no_panic.py.
    x: int = 2 ** 4294967296
    assert x == 0


if __name__ == "__main__":
    test_pow_no_panic()

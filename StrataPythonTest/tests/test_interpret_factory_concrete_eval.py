#
# `pyInterpret` used to initialize its runtime evaluator without the
# Python-specific factory (PyFactory / RuntimeFactory). Now that
# RuntimeFactory is passed to Core.Program.run, front-end factory functions
# with a `concreteEval` — int_pow, int_rshift, int_lshift — evaluate them at
# run time, so the asserts in this program can be decided.
#
def test_concrete_eval():
    # Cover the three factory functions currently registered in RuntimeFactory
    # that carry a concreteEval: int_pow (**), int_rshift (>>), int_lshift
    # (<<, routed through int_pow(2, n)). Combining them into a single
    # arithmetic expression ensures the fix applies end-to-end, not just to
    # a single top-level call.
    a: int = 2 ** 10       # int_pow(2, 10) = 1024
    b: int = 1 << 4        # int_lshift → int_pow(2, 4) = 16
    c: int = 256 >> 3      # int_rshift(256, 3) = 32
    d: int = 3 ** 4        # int_pow(3, 4) = 81
    assert a == 1024
    assert b == 16
    assert c == 32
    assert d == 81
    # Combined: sum should be 1024 + 16 + 32 + 81 = 1153
    assert a + b + c + d == 1153


if __name__ == "__main__":
    test_concrete_eval()

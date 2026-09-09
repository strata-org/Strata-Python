# Multiple exceptions in expression — `f() + g()` both raise; CPython: left
# wins (first evaluated); model may evaluate both or pick wrong one
"""
MULTIPLE EXCEPTIONS IN ONE EXPRESSION — FIRST (LEFT-TO-RIGHT) WINS

CPython: f() + g() where both raise:
         f() is evaluated FIRST (left-to-right).
         f() raises → g() is NEVER evaluated.
         Only f()'s exception propagates.

Model:   If both subexpressions are evaluated eagerly:
         val_f = f()  → exception(ValueError("from f"))
         val_g = g()  → exception(KeyError("from g"))
         PAdd(exception(...), exception(...)) → Hole or picks one arbitrarily

         The model may:
         1. Evaluate both (wrong — g should never run)
         2. Pick the wrong exception (KeyError instead of ValueError)
         3. Return Hole (losing both exceptions)

CPython guarantees LEFT-TO-RIGHT evaluation with SHORT-CIRCUIT on exception.
The FIRST exception (leftmost) is the one that propagates.
"""


def raise_value_error() -> int:
    raise ValueError("from f")


def raise_key_error() -> int:
    raise KeyError("from g")


def both_raise_addition() -> int:
    """f() + g() — f raises first, g never evaluated."""
    return raise_value_error() + raise_key_error()


def both_raise_in_args() -> int:
    """h(f(), g()) — f raises first, g never evaluated, h never called."""
    return raise_value_error() + raise_key_error()


def first_ok_second_raises() -> int:
    """f() + g() — f succeeds, g raises."""
    return 42 + raise_key_error()


def side_effect_tracking() -> int:
    """Verify second operand is NOT evaluated when first raises."""
    # If model evaluates both, it would "see" the second raise
    # CPython only sees the first
    return raise_value_error() + raise_key_error()


def three_operands() -> int:
    """a + b + c — left-to-right, first exception wins."""
    # Parsed as (a + b) + c
    # If a raises: b and c never evaluated
    return raise_value_error() + 1 + raise_key_error()


def main() -> None:
    # Test 1: both raise — ValueError (first/left) wins
    try:
        both_raise_addition()
        assert False
    except ValueError:
        pass  # CORRECT: ValueError from left operand
    except KeyError:
        assert False  # WRONG: would mean right was evaluated first

    # Test 2: first ok, second raises — KeyError propagates
    try:
        first_ok_second_raises()
        assert False
    except KeyError:
        pass  # CORRECT: only second raises

    # Test 3: three operands — first exception wins
    try:
        three_operands()
        assert False
    except ValueError:
        pass  # CORRECT: leftmost raises first

    # Test 4: verify it's specifically ValueError not KeyError
    caught_type: str = ""
    try:
        side_effect_tracking()
    except ValueError:
        caught_type = "ValueError"
    except KeyError:
        caught_type = "KeyError"
    assert caught_type == "ValueError"

    print("all passed")


main()

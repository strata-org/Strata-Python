# Exception in augmented assign RHS — `x += raises()` must NOT assign to x;
# naive desugar `x = x + raises()` overwrites x with Hole/exception; target
# must retain old value
"""
EXCEPTION IN AUGMENTED ASSIGN RHS — PARTIAL EVALUATION LEAVES TARGET STALE

The subset allows:
  - Augmented assignment (IN): x += expr, d[k] += expr, obj.f += expr
  - Exceptions from function calls (IN)
  - try/except (IN)

The NOVEL gap: augmented assignment `target += expr` where `expr` raises.

CPython evaluation order for `x += f()`:
  1. Evaluate x (read current value)
  2. Evaluate f() — THIS RAISES
  3. Never reaches the addition or assignment
  4. x retains its OLD value

CPython evaluation order for `d[k] += f()`:
  1. Evaluate d[k] (read current value)
  2. Evaluate f() — THIS RAISES
  3. Never reaches addition or assignment
  4. d[k] retains its old value

The model's translation of `x += f()`:
  - Naive: `x = PAdd(x, f())` — if f() returns exception tag, PAdd gets
    exception as operand → Hole (finding 079) or exception propagates
  - But the ASSIGNMENT still happens: `x = Hole` or `x = exception(...)`
  - CPython: x is UNCHANGED (assignment never executed)

This creates a divergence:
  - CPython: x retains pre-augmented-assign value
  - Model: x gets Hole or exception value (WRONG)

The fix requires: if RHS evaluation produces exception, the assignment
must NOT execute. This is the augmented-assign-specific version of
finding 386 (exception in function argument), but with the additional
complication that the TARGET has already been read.

For compound targets (`d[k] += f()`, `obj.field += f()`):
  - The target evaluation (step 1) may have SIDE EFFECTS in CPython
    (e.g., __getitem__ with side effects) — but in Frontend subset,
    all reads are pure, so this is not an issue
  - The key issue is: the WRITE-BACK must not happen if RHS raises

DISTINCT FROM:
  - Finding 079 (exception poisons operators) — that's about exception
    flowing INTO PAdd; this is about the ASSIGNMENT not happening
  - Finding 386 (exception in function argument) — that's about call
    arguments; this is about augmented assignment specifically
  - Finding 048 (augmented assign on fields) — that's about rebinding;
    this is about exception interrupting the augmented assign
  - Finding 336 (augmented assign dict subscript) — that's about the
    4-step read-modify-write; this is about exception in the RHS
"""
from dataclasses import dataclass


def might_raise(x: int) -> int:
    if x < 0:
        raise ValueError("negative")
    return x * 2


def augmented_assign_rhs_raises(n: int) -> int:
    """Augmented assign where RHS function raises.
    
    CPython: total unchanged when might_raise raises
    Model: total may become Hole or exception value
    """
    total: int = 100
    try:
        total += might_raise(n)
        # If n >= 0: total = 100 + n*2
        # If n < 0: might_raise raises, total stays 100
    except ValueError:
        pass
    return total


def dict_augmented_rhs_raises(key: str, delta: int) -> int:
    """Dict augmented assign where RHS raises.
    
    CPython: d[key] unchanged when might_raise raises
    Model: d[key] may become Hole
    """
    d: dict[str, int] = {"count": 10, "total": 50}
    try:
        d[key] += might_raise(delta)
    except ValueError:
        pass
    return d[key]


@dataclass
class Accumulator:
    value: int
    count: int


def field_augmented_rhs_raises(acc: Accumulator, delta: int) -> int:
    """Field augmented assign where RHS raises.
    
    CPython: acc.value unchanged when might_raise raises
    Model: acc.value may become Hole after failed augmented assign
    """
    try:
        new_value: int = acc.value + might_raise(delta)
        acc = Accumulator(value=new_value, count=acc.count + 1)
    except ValueError:
        pass
    return acc.value


def chained_augmented_partial(a: int, b: int) -> tuple[int, int]:
    """Two augmented assigns — first succeeds, second raises.
    
    CPython: x updated by first, y unchanged by second
    Model: if exception propagation wrong, both or neither update
    """
    x: int = 0
    y: int = 0
    try:
        x += might_raise(a)  # succeeds if a >= 0
        y += might_raise(b)  # raises if b < 0
    except ValueError:
        pass
    return (x, y)


def main() -> None:
    # Test 1: RHS raises, target unchanged
    r1: int = augmented_assign_rhs_raises(5)
    assert r1 == 110  # 100 + 5*2 = 110 (no exception)

    r2: int = augmented_assign_rhs_raises(-3)
    assert r2 == 100  # Exception raised, total stays 100
    # Model risk: total becomes Hole or exception value → assertion fails

    # Test 2: Dict augmented assign RHS raises
    r3: int = dict_augmented_rhs_raises("count", 5)
    assert r3 == 20  # 10 + 5*2 = 20

    r4: int = dict_augmented_rhs_raises("count", -1)
    assert r4 == 10  # Exception, d["count"] stays 10
    # Model risk: d["count"] becomes Hole

    # Test 3: Field augmented assign RHS raises
    acc: Accumulator = Accumulator(value=50, count=0)
    r5: int = field_augmented_rhs_raises(acc, 3)
    assert r5 == 56  # 50 + 3*2 = 56

    r6: int = field_augmented_rhs_raises(acc, -1)
    assert r6 == 50  # Exception, acc.value stays 50
    # Model risk: acc.value becomes Hole

    # Test 4: Partial execution — first succeeds, second raises
    pair: tuple[int, int] = chained_augmented_partial(5, -1)
    assert pair[0] == 10  # x = 0 + 5*2 = 10 (succeeded)
    assert pair[1] == 0   # y unchanged (second raise)
    # Model risk: if exception handling wrong, x also unchanged (0)
    # or y also updated (wrong)

    print("all assertions passed")


main()

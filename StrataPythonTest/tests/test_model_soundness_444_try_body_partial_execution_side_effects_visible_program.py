# Try body partial execution — statements before exception point have visible
# side effects in handler; model either runs all (274) or none (atomic)
"""
TRY BODY PARTIAL EXECUTION — SIDE EFFECTS BEFORE EXCEPTION ARE VISIBLE

DIVERGENCE:
  CPython:  In a try body with multiple statements, if statement N raises,
            statements 1..N-1 have ALREADY EXECUTED (their side effects
            are visible in the except handler and after).
  Model:    The exception-as-value model may either:
            (a) Execute ALL statements (exception doesn't stop execution)
            (b) Execute NO statements (treats try body as atomic)
            Neither correctly models partial execution.

This is a refinement of finding 274 (exception doesn't terminate).
Finding 274 shows that statements AFTER the raise still execute.
This finding shows the CONVERSE: statements BEFORE the raise MUST
have their effects preserved in the handler.

ROOT CAUSE: The exception-as-value model has no concept of "execution
stopped at statement N." It either runs everything or nothing.
"""
from dataclasses import dataclass


@dataclass
class State:
    count: int
    last_value: int


def partial_execution_visible(items: list[int]) -> State:
    """Process items; exception at item N means items 0..N-1 were processed."""
    state: State = State(count=0, last_value=0)
    try:
        for item in items:
            if item < 0:
                raise ValueError("negative item")
            # These assignments happen for items BEFORE the negative one
            state = State(count=state.count + 1, last_value=item)
    except ValueError:
        pass
    # CPython: state reflects all items processed BEFORE the exception
    # Model: state may be initial (if try body treated as atomic)
    #         or reflect ALL items (if exception doesn't stop loop)
    return state


def sequential_effects_before_raise(x: int) -> int:
    """Multiple assignments before a conditional raise."""
    a: int = 0
    b: int = 0
    try:
        a = x * 2          # always executes
        b = a + 10         # always executes
        if x > 5:
            raise ValueError("too large")
        b = b + 100        # only executes if x <= 5
    except ValueError:
        pass
    # CPython when x=7: a=14, b=24 (b=14+10, raise before b+100)
    # CPython when x=3: a=6, b=116 (b=6+10+100, no raise)
    # Model: depends on how exception-as-value interacts with assignments
    return a + b


def handler_sees_partial_state(items: list[int]) -> int:
    """The except handler can read variables set before the exception."""
    processed: int = 0
    last_good: int = -1
    try:
        for item in items:
            if item == 0:
                raise ValueError("zero found")
            processed = processed + 1
            last_good = item
    except ValueError:
        # CPython: processed and last_good reflect items before the zero
        # Model: may see initial values (0, -1) if partial execution lost
        return processed * 1000 + last_good
    return processed * 1000 + last_good


def accumulator_before_exception(n: int) -> int:
    """Accumulate values, raise partway through."""
    total: int = 0
    try:
        i: int = 0
        while i < n:
            if i == 3:
                raise ValueError("stopped at 3")
            total = total + i  # 0 + 1 + 2 = 3 before raise
            i = i + 1
    except ValueError:
        pass
    # CPython: total = 0 + 1 + 2 = 3 (accumulated before i==3)
    # Model: total may be 0 (no execution) or wrong value
    return total


def main() -> None:
    # Test 1: partial execution in loop
    s1: State = partial_execution_visible([1, 2, 3, -1, 5])
    # Processed 1, 2, 3 before hitting -1
    assert s1.count == 3
    assert s1.last_value == 3

    # Test 2: sequential effects
    assert sequential_effects_before_raise(7) == 14 + 24  # a=14, b=24
    assert sequential_effects_before_raise(3) == 6 + 116  # a=6, b=116

    # Test 3: handler reads partial state
    result: int = handler_sees_partial_state([10, 20, 0, 30])
    # processed=2, last_good=20 → 2000 + 20 = 2020
    assert result == 2020

    # Test 4: accumulator
    assert accumulator_before_exception(10) == 3  # 0+1+2

    print("all passed")


main()

# While loop condition reads object field, body rebinds object — condition may
# read STALE pre-rebind value; loop appears infinite or post-loop properties
# unprovable
"""
WHILE LOOP CONDITION READS OBJECT FIELD — BODY MODIFIES FIELD — STALE CONDITION

The subset allows:
  - while loops with conditions (IN)
  - @dataclass field access in conditions (IN)
  - Field write + rebinding in loop body (IN, finding 211)
  - Comparison operators (IN)

The NOVEL gap: when a while loop's condition reads an object field,
and the loop body modifies that field (with proper rebinding), the
NEXT iteration's condition evaluation must read the UPDATED field.
Under value semantics with rebinding, this requires the condition
to re-read from the REBOUND variable, not the original.

  @dataclass
  class Counter:
      value: int
      limit: int

  c = Counter(value=0, limit=5)
  while c.value < c.limit:
      c = Counter(value=c.value + 1, limit=c.limit)
  # CPython: loop runs 5 times, c.value == 5
  # Model risk: condition reads ORIGINAL c (value=0 < limit=5 = True FOREVER)

If the translator evaluates the condition using the variable binding
from BEFORE the loop body executes (stale binding), the condition
never changes and the loop either:
  - Runs forever (if model tracks termination)
  - Is unrolled with always-true condition (unsound: proves post-loop
    properties that assume the loop ran, but condition was never false)

ROOT CAUSE: The while loop translation must ensure that:
  1. The condition is evaluated using the CURRENT binding of all variables
  2. After the body executes and rebinds variables, the back-edge
     re-evaluates the condition with the NEW bindings
  3. The exit assume uses the FINAL binding's field values

This is related to but distinct from:
  - Finding 049 (while condition re-evaluation with object mutation) —
    that's about MUTATION (which is lost under value semantics);
    THIS is about REBINDING (which should work but may not)
  - Finding 169 (while exit condition not assumed) — that's about
    the post-loop assume; this is about the condition evaluation itself
  - Finding 414 (while counter final value) — that's about simple int
    counters; this is about OBJECT FIELDS in the condition

The key insight: with value semantics + rebinding, the loop SHOULD work
correctly IF the translator properly threads the rebound variable back
to the condition. But if the condition is translated as a fixed expression
referencing the INITIAL variable (before any rebinding), it's stale.
"""
from dataclasses import dataclass


@dataclass
class Counter:
    value: int
    limit: int

    def is_done(self: "Counter") -> bool:
        return self.value >= self.limit


@dataclass
class Accumulator:
    total: int
    count: int


def count_to_limit() -> int:
    """While loop with object field in condition, body rebinds object.
    
    CPython: loop runs 5 times, returns 5
    Model risk: if condition reads stale 'c', loop is infinite or
    post-loop c.value is unprovable
    """
    c: Counter = Counter(value=0, limit=5)
    while c.value < c.limit:
        c = Counter(value=c.value + 1, limit=c.limit)
    return c.value  # Should be 5


def accumulate_until_threshold(items: list[int], threshold: int) -> int:
    """Accumulator object modified in loop, condition reads its field.
    
    CPython: accumulates until total >= threshold
    Model: must re-read acc.total from rebound acc each iteration
    """
    acc: Accumulator = Accumulator(total=0, count=0)
    i: int = 0
    while acc.total < threshold and i < len(items):
        acc = Accumulator(total=acc.total + items[i], count=acc.count + 1)
        i = i + 1
    return acc.total


def method_in_condition() -> int:
    """Method call in while condition — must use rebound receiver.
    
    CPython: c.is_done() re-evaluates on current c each iteration
    Model: if method dispatches on ORIGINAL c, always returns False
    """
    c: Counter = Counter(value=0, limit=3)
    iterations: int = 0
    while not c.is_done():
        c = Counter(value=c.value + 1, limit=c.limit)
        iterations = iterations + 1
    return iterations  # Should be 3


def nested_field_in_condition() -> int:
    """Condition reads field, body modifies DIFFERENT field too.
    
    Tests that rebinding preserves ALL fields, not just the modified one.
    """
    c: Counter = Counter(value=0, limit=10)
    total: int = 0
    while c.value < c.limit:
        total = total + c.value
        # Modify value, preserve limit
        c = Counter(value=c.value + 2, limit=c.limit)
    # c.value should be 10 (0, 2, 4, 6, 8, 10 — exits when 10 < 10 is False)
    return total  # 0 + 2 + 4 + 6 + 8 = 20


def decreasing_loop() -> int:
    """Loop where field DECREASES — condition must see decrease.
    
    If condition reads stale (initial) value, it sees limit > 0 forever.
    """
    c: Counter = Counter(value=10, limit=10)
    steps: int = 0
    while c.value > 0:
        c = Counter(value=c.value - 3, limit=c.limit)
        steps = steps + 1
    # c.value goes: 10, 7, 4, 1, -2 (exits when -2 > 0 is False)
    return steps  # 4 iterations


def main() -> None:
    assert count_to_limit() == 5
    
    items: list[int] = [3, 5, 2, 8, 1]
    assert accumulate_until_threshold(items, 10) == 10  # 3+5+2=10
    assert accumulate_until_threshold(items, 100) == 19  # sum all
    
    assert method_in_condition() == 3
    assert nested_field_in_condition() == 20
    assert decreasing_loop() == 4

    print("all passed")


main()

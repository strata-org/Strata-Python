# Exception in for-loop iterable expression — `for x in f():` where f()
# raises; model enters loop with Hole iterable; no propagation check at loop
# entry
"""
EXCEPTION IN FOR-LOOP ITERABLE EXPRESSION — LOOP BODY EXECUTES ON HOLE

The subset allows:
  - for loops (IN)
  - Function calls in expressions (IN)
  - Exceptions (IN)

The NOVEL gap: when the ITERABLE expression in a for-loop raises an
exception, the loop body must NOT execute. But if the exception-as-value
model doesn't check the iterable's tag before entering the loop, the
loop may iterate over an exception value.

  def get_items() -> list[int]:
      raise ValueError("no items")

  total: int = 0
  for x in get_items():  # get_items() raises!
      total += x
  # CPython: ValueError propagates, loop body never executes, total stays 0
  # Model: get_items() returns exception(...), for-loop iterates over it
  #         → x = ??? (undefined behavior on exception tag)
  #         → total += x → Hole or garbage

This is distinct from:
  - Finding 274 (exception no propagation) — that's about exceptions
    INSIDE the loop body
  - Finding 386 (exception in function argument) — that's about args
  - Finding 389 (exception in condition) — that's about if/while conditions
  - Finding 456 (exception + for/else) — that's about the else clause

This finding is about the ITERABLE EXPRESSION itself raising. The
exception must propagate BEFORE the loop begins. No iteration occurs.

The model likely translates `for x in expr:` as:
  _iter = expr
  _i = 0
  while _i < List_len(_iter):
      x = List_get(_iter, _i)
      <body>
      _i += 1

If `expr` evaluates to `exception(...)`, then:
  - `List_len(exception(...))` → Hole (no case for exception tag)
  - `_i < Hole` → Hole (comparison with Hole)
  - Loop condition is Hole → solver may explore both branches
  - Loop body may execute with x = Hole

Similarly for range-based loops:
  for i in range(f()):  # f() raises
      ...
  # CPython: exception propagates, no iteration
  # Model: range(exception(...)) → Hole → loop behavior undefined
"""
from dataclasses import dataclass


def get_positive_items(xs: list[int]) -> list[int]:
    """Returns items if all positive, raises if any negative."""
    for x in xs:
        if x < 0:
            raise ValueError("negative element")
    return xs


def get_count(n: int) -> int:
    """Returns n if positive, raises if not."""
    if n <= 0:
        raise ValueError("count must be positive")
    return n


def sum_validated_items(xs: list[int]) -> int:
    """Sum items from a validating function.
    
    CPython: if get_positive_items raises, loop never executes, 
             exception propagates to caller.
    Model: if exception flows into for-loop iterable position,
           loop may execute with garbage values.
    """
    total: int = 0
    for x in get_positive_items(xs):
        total += x
    return total


def count_range(n: int) -> int:
    """Count iterations of range(get_count(n)).
    
    CPython: if get_count raises, range() never called, no iterations.
    Model: range(exception(...)) → undefined loop behavior.
    """
    count: int = 0
    for i in range(get_count(n)):
        count += 1
    return count


def nested_exception_in_iterable(xs: list[int], ys: list[int]) -> int:
    """Outer loop iterates, inner loop's iterable may raise.
    
    CPython: outer loop runs until inner iterable raises, then propagates.
    Model: inner exception may not terminate outer loop.
    """
    total: int = 0
    for x in xs:
        for y in get_positive_items(ys):
            total += x + y
    return total


def exception_in_range_stop(items: list[int]) -> int:
    """range(len(get_positive_items(items))) — exception in nested call.
    
    The exception occurs deep in the expression that computes the
    range stop value. Must propagate before any iteration.
    """
    total: int = 0
    validated: list[int] = get_positive_items(items)
    for i in range(len(validated)):
        total += validated[i]
    return total


def main() -> None:
    # Normal case: no exception, loop executes
    assert sum_validated_items([1, 2, 3]) == 6
    assert count_range(5) == 5

    # Exception in iterable: loop must NOT execute
    caught1: bool = False
    try:
        sum_validated_items([1, -2, 3])
        assert False  # should not reach here
    except ValueError:
        caught1 = True
    assert caught1

    # Exception in range argument: loop must NOT execute
    caught2: bool = False
    try:
        count_range(-1)
        assert False
    except ValueError:
        caught2 = True
    assert caught2

    # Nested: inner iterable raises
    caught3: bool = False
    try:
        nested_exception_in_iterable([1, 2], [3, -4, 5])
        assert False
    except ValueError:
        caught3 = True
    assert caught3

    # Exception in range stop computation
    caught4: bool = False
    try:
        exception_in_range_stop([1, -2, 3])
        assert False
    except ValueError:
        caught4 = True
    assert caught4

    # Normal nested case works
    assert nested_exception_in_iterable([1, 2], [3, 4]) == 20
    # (1+3) + (1+4) + (2+3) + (2+4) = 4+5+5+6 = 20

    print("all passed")


main()

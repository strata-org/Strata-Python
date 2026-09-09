# isinstance narrowing not killed at loop back-edge — narrowing from iteration
# K leaks to K+1; model OVER-PROVES (thinks all elements are narrowed type);
# UNSOUND
"""
ISINSTANCE NARROWING NOT KILLED AT LOOP BACK-EDGE — OVER-PROVES

The subset allows:
  - isinstance narrowing (IN)
  - while loops (IN)
  - Optional[T] variables reassigned in loop body (IN)
  - Single inheritance (IN)

The NOVEL gap: when isinstance narrows a variable inside a loop body,
that narrowing must be KILLED at the loop back-edge because the variable
may be reassigned to a different type on the next iteration.

  from typing import Optional

  def process(items: list[Optional[int]]) -> int:
      total: int = 0
      i: int = 0
      while i < len(items):
          x: Optional[int] = items[i]
          if x is not None:
              total = total + x  # narrowed: x is int here
          # At back-edge: x is reassigned next iteration
          # Narrowing from this iteration must NOT carry to next
          i = i + 1
      return total

This specific case is SOUND because x is reassigned at loop top.
But the UNSOUND case is:

  def find_first_int(items: list[Optional[int]]) -> int:
      result: Optional[int] = None
      i: int = 0
      while i < len(items):
          if result is not None:
              return result  # narrowed: result is int
          result = items[i]  # may be None or int
          i = i + 1
      # Here: result may be None (last element was None)
      # Model may INCORRECTLY assume result is int (narrowing leaked)
      if result is not None:
          return result
      return -1

The critical issue: if the model's narrowing from `if result is not None`
on iteration K persists to iteration K+1's entry, the model incorrectly
assumes result is always int after the first successful narrowing.

ROOT CAUSE: The translator emits `assume(!isfrom_None(result))` inside
the if-branch. At the loop back-edge, this assumption must be KILLED
because `result = items[i]` may reassign result to None. If the model
uses a simple SSA form without phi-nodes at loop headers, the narrowing
from one iteration leaks into the next.

This is distinct from:
  - Finding 162 (narrowing invalidated by reassignment) — that's about
    SEQUENTIAL code, not loop back-edges
  - Finding 334 (narrowing killed at branch merge) — that's about
    if/else merge, not loop iteration
  - Finding 459 (narrowing killed by method call) — that's about
    conservative invalidation, not loop structure

The loop back-edge is special because it creates a CYCLE in the CFG.
Narrowing that's valid on one path through the cycle may be invalid
on the next traversal.
"""
from dataclasses import dataclass
from typing import Optional


@dataclass
class Animal:
    name: str


@dataclass
class Dog(Animal):
    tricks: int


def count_dogs_wrong(animals: list[Animal]) -> int:
    """Demonstrates narrowing that must be killed each iteration.
    
    If narrowing from isinstance(animal, Dog) on iteration K
    persists to iteration K+1, the model thinks ALL animals are Dogs
    after the first Dog is found.
    """
    count: int = 0
    i: int = 0
    while i < len(animals):
        animal: Animal = animals[i]
        if isinstance(animal, Dog):
            # Narrowed: animal is Dog here
            count = count + 1
            # This narrowing must NOT persist to next iteration
        # At back-edge: animal will be reassigned from animals[i+1]
        # which may be a plain Animal, not a Dog
        i = i + 1
    return count


def find_first_with_tricks(animals: list[Animal], min_tricks: int) -> Optional[str]:
    """Narrowing inside loop with early return.
    
    The narrowing from isinstance must be fresh each iteration.
    If it leaks, the model thinks animal.tricks is always accessible.
    """
    i: int = 0
    while i < len(animals):
        animal: Animal = animals[i]
        if isinstance(animal, Dog):
            if animal.tricks >= min_tricks:
                return animal.name
        # If narrowing leaks: model thinks animal is ALWAYS Dog here
        # and animal.tricks is accessible — WRONG for plain Animal
        i = i + 1
    return None


def accumulate_with_narrowing(values: list[Optional[int]]) -> int:
    """Optional narrowing that must reset each iteration.
    
    CPython: processes each element independently
    Model risk: narrowing from iteration where value is not None
    persists, making model think value is NEVER None after first hit.
    """
    total: int = 0
    found_any: bool = False
    i: int = 0
    while i < len(values):
        value: Optional[int] = values[i]
        if value is not None:
            total = total + value
            found_any = True
        # Narrowing of 'value' must die here — next iteration
        # value = values[i+1] which may be None
        i = i + 1
    if found_any:
        return total
    return -1


def narrowing_across_reassignment(items: list[Optional[int]]) -> int:
    """The CRITICAL case: variable narrowed, then reassigned, then
    narrowing from PREVIOUS iteration incorrectly assumed.
    
    CPython: each iteration starts fresh
    Model (if buggy): assumes 'current' is int after first non-None
    """
    current: Optional[int] = None
    total: int = 0
    i: int = 0
    while i < len(items):
        # If narrowing from previous iteration leaked:
        # model thinks current is int here (WRONG on first iteration
        # and after any None element)
        if current is not None:
            total = total + current
        current = items[i]  # reassignment — may be None
        i = i + 1
    # Final element
    if current is not None:
        total = total + current
    return total


def main() -> None:
    # count_dogs_wrong
    animals: list[Animal] = [
        Dog(name="Rex", tricks=3),
        Animal(name="Cat"),
        Dog(name="Buddy", tricks=5),
        Animal(name="Bird"),
    ]
    assert count_dogs_wrong(animals) == 2

    # find_first_with_tricks
    result: Optional[str] = find_first_with_tricks(animals, 4)
    assert result == "Buddy"

    no_result: Optional[str] = find_first_with_tricks(animals, 10)
    assert no_result is None

    # accumulate_with_narrowing
    values: list[Optional[int]] = [1, None, 3, None, 5]
    assert accumulate_with_narrowing(values) == 9

    empty_values: list[Optional[int]] = [None, None]
    assert accumulate_with_narrowing(empty_values) == -1

    # narrowing_across_reassignment
    items: list[Optional[int]] = [1, 2, None, 4, 5]
    # Process: current starts None, then 1, 2, None, 4, 5
    # Totals: 0, +1, +2, +0(None), +0(None was current), +4
    # Wait: iteration 0: current=None(skip), current=1
    #        iteration 1: current=1(add 1), current=2
    #        iteration 2: current=2(add 2), current=None
    #        iteration 3: current=None(skip), current=4
    #        iteration 4: current=4(add 4), current=5
    # After loop: current=5(add 5)
    # Total: 1 + 2 + 4 + 5 = 12
    assert narrowing_across_reassignment(items) == 12

    print("all passed")


main()

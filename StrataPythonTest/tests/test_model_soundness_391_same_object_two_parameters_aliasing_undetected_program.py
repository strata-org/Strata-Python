# Same object as two function params `f(obj, obj)` — hidden alias; SOUND under
# functional style (no mutation), latent bug if mutation added
"""
SAME OBJECT PASSED AS TWO PARAMETERS — ALIASING UNDETECTED

CPython: def f(a: Point, b: Point): a.x = 99; return b.x
         f(obj, obj) → 99 (a and b are the SAME object!)

Model:   f receives two INDEPENDENT copies of obj.
         Modifying a.x doesn't affect b.x.
         f(obj, obj) → obj.x (original value, not 99)

The subset bans `b = a` (direct alias). But passing the SAME
object as two different parameters creates an alias that the
AST checker may NOT detect — it looks like two different variables
at the call site.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


def swap_fields(a: Point, b: Point) -> Point:
    """If a and b are same object, this is a self-swap (no-op in CPython)."""
    temp: int = a.x
    # In functional style, we'd return new Points
    # But conceptually: if a IS b, reading b.x after "writing" a.x
    # should see the new value
    return Point(b.x, a.y)


def modify_first_read_second(a: Point, b: Point) -> int:
    """Modify a, read b — if aliased, b sees the change."""
    new_a: Point = Point(99, a.y)
    # In CPython with aliasing: b.x would be 99
    # In model: b is independent copy, b.x is original
    return b.x


def same_object_two_params() -> int:
    """Pass same object as both params — creates hidden alias."""
    p: Point = Point(1, 2)
    # CPython: modify_first_read_second(p, p)
    #   a and b are SAME object
    #   "modifying a" and "reading b" access same memory
    #   Returns 1 (original x, since we return new Point not mutate)
    result: int = modify_first_read_second(p, p)
    # Under value semantics: a and b are independent copies
    # Result is the same (1) because we use functional style
    return result


def aliased_accumulate(acc: Point, delta: Point) -> Point:
    """If acc IS delta, result depends on aliasing."""
    return Point(acc.x + delta.x, acc.y + delta.y)


def main() -> None:
    # Test 1: same object as two params (functional style — both agree)
    p: Point = Point(5, 10)
    result: int = modify_first_read_second(p, p)
    # Both CPython and model: 5 (functional style doesn't mutate)
    assert result == 5

    # Test 2: accumulate with self-alias
    p2: Point = Point(3, 4)
    acc: Point = aliased_accumulate(p2, p2)
    # CPython: Point(6, 8) — p2.x + p2.x = 6
    # Model: same — functional style, no mutation
    assert acc.x == 6 and acc.y == 8

    # Test 3: the DANGEROUS case (if mutation were allowed)
    # Under the subset's no-mutation rule, this is safe
    # But if the subset ever allows mutation:
    #   def mutate_first(a, b): a.x = 99; return b.x
    #   mutate_first(p, p) → CPython: 99, Model: original
    # The AST checker must detect f(x, x) as potential aliasing

    print("all passed")


main()

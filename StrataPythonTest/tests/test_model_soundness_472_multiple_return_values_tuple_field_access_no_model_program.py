# Tuple element access by index `t[0]` — subscript dispatch has no tuple case;
# even with ClassInstance encoding, `Any_get!` doesn't handle tuple-as-
# ClassInstance
"""
TUPLE RETURN FROM FUNCTION — CALLER ACCESSES ELEMENTS — NO TUPLE MODEL

The subset allows:
  - tuple[T1, T2, ...] with explicit types (IN)
  - Functions returning tuples (IN, via finding 218 ClassInstance encoding)
  - Tuple unpacking `a, b = f()` (IN, finding 458)

The NOVEL gap: accessing tuple elements BY INDEX after function return,
WITHOUT unpacking. The subset allows `t[0]`, `t[1]` on tuples.

    def min_max(xs: list[int]) -> tuple[int, int]:
        return (min(xs), max(xs))

    result: tuple[int, int] = min_max([3, 1, 4])
    lo: int = result[0]   # CPython: 1
    hi: int = result[1]   # CPython: 4

Finding 218 proposes encoding tuples as ClassInstance with _0, _1 fields.
Finding 458 covers tuple UNPACKING (`a, b = f()`).

THIS finding covers the case where the tuple is stored in a variable
and then accessed by INDEX. The model must:
  1. Know that `result` has tag from_ClassInstance (or whatever tuple encoding)
  2. Translate `result[0]` to field access on the tuple encoding
  3. Assert the correct element type (int) on the accessed value

If tuples are encoded as ClassInstance("tuple_2", {"_0": v0, "_1": v1}):
  - `result[0]` → DictStrAny_get(result.attrs, "_0") → needs McCarthy axiom
  - `result[1]` → DictStrAny_get(result.attrs, "_1") → needs McCarthy axiom
  - Type assertion: isfrom_int(result[0]) needed but not emitted

If tuples have NO encoding (finding 028):
  - `result` is Hole
  - `result[0]` is Hole
  - All downstream computation is Hole

The INTERACTION: even if finding 218's encoding is implemented,
the SUBSCRIPT operator `t[i]` must be translated differently for
tuples than for lists:
  - List: List_get(xs, i) with bounds check
  - Tuple: DictStrAny_get(attrs, str(i)) with field-presence axiom
  - String: str_char_at(s, i)

The translator must dispatch `Any_get!` based on the STATIC TYPE
of the container, not just the runtime tag. Without static type info,
`result[0]` goes through the generic subscript path which may not
handle the tuple encoding.
"""
from dataclasses import dataclass


def divmod_manual(a: int, b: int) -> tuple[int, int]:
    """Return (quotient, remainder).
    
    CPython: returns a tuple (a//b, a%b)
    Model: if tuple has no encoding, returns Hole
    """
    q: int = a // b
    r: int = a % b
    return (q, r)


def min_max(xs: list[int]) -> tuple[int, int]:
    """Return (minimum, maximum) of a non-empty list.
    
    CPython: returns tuple of two ints
    Model: tuple construction may produce Hole or untyped ClassInstance
    """
    lo: int = xs[0]
    hi: int = xs[0]
    for x in xs:
        if x < lo:
            lo = x
        if x > hi:
            hi = x
    return (lo, hi)


def use_tuple_by_index(values: list[int]) -> int:
    """Access tuple elements by index (not unpacking).
    
    CPython: result[0] and result[1] are ints
    Model risk: subscript on tuple encoding fails or returns Hole
    """
    result: tuple[int, int] = min_max(values)
    # Access by index — NOT unpacking
    lo: int = result[0]
    hi: int = result[1]
    return hi - lo


def tuple_in_condition(pair: tuple[int, int]) -> bool:
    """Use tuple element in boolean condition.
    
    CPython: pair[0] is int, comparison works
    Model: if pair[0] is Hole, condition is non-deterministic
    """
    return pair[0] > pair[1]


def nested_tuple_access(data: list[int]) -> int:
    """Chain: function returns tuple, caller indexes, uses in arithmetic.
    
    Full chain: min_max() → tuple → [0] → int → arithmetic
    Any break in chain → Hole propagates to final result
    """
    bounds: tuple[int, int] = min_max(data)
    spread: int = bounds[1] - bounds[0]
    midpoint: int = bounds[0] + spread // 2
    return midpoint


def main() -> None:
    # Test divmod_manual
    dm: tuple[int, int] = divmod_manual(17, 5)
    assert dm[0] == 3   # quotient
    assert dm[1] == 2   # remainder
    # Model risk: dm[0] is Hole → assertion unprovable

    # Test min_max
    mm: tuple[int, int] = min_max([3, 1, 4, 1, 5])
    assert mm[0] == 1   # min
    assert mm[1] == 5   # max

    # Test use_tuple_by_index
    spread: int = use_tuple_by_index([3, 1, 4, 1, 5])
    assert spread == 4  # 5 - 1

    # Test tuple_in_condition
    assert tuple_in_condition((10, 5)) == True
    assert tuple_in_condition((3, 7)) == False

    # Test nested_tuple_access
    mid: int = nested_tuple_access([2, 8])
    # min=2, max=8, spread=6, midpoint=2+3=5
    assert mid == 5

    print("all assertions passed")


main()

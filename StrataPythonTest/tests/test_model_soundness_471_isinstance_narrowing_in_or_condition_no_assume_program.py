# isinstance in OR/AND compound condition — `isinstance(x,int) or
# isinstance(x,str)` needs disjunctive assume; single-isinstance extraction
# misses compound narrowing
"""
ISINSTANCE NARROWING IN OR-CONDITION — NO ASSUME EMITTED

The subset allows:
  - isinstance (IN)
  - or/and boolean operators (IN)
  - Optional narrowing (IN)
  - if/elif/else (IN)

The NOVEL gap: isinstance used in a COMPOUND condition with `or`:

    if isinstance(x, int) or isinstance(x, str):
        # CPython: x is int OR str — both branches valid
        # Model: what assume is emitted?

The model's narrowing mechanism works by emitting:
    assume(isfrom_int(x))  — after `isinstance(x, int)` guard

But with `or`:
    isinstance(x, int) or isinstance(x, str)

The DISJUNCTION means the assume must be:
    assume(isfrom_int(x) || isfrom_str(x))

If the translator:
1. Only handles single isinstance in condition → no narrowing at all (Hole)
2. Takes the FIRST isinstance → assume(isfrom_int(x)) only (UNSOUND: rejects valid str values)
3. Takes the LAST isinstance → assume(isfrom_str(x)) only (UNSOUND: rejects valid int values)

Similarly for `and` with negation:
    if not isinstance(x, int) and not isinstance(x, str):
        # x is neither int nor str
    else:
        # x IS int or str — same disjunctive narrowing needed

This is DISTINCT from:
  - Finding 302 (isinstance tuple-of-types) — that's `isinstance(x, (int, str))`
    which is a SINGLE call with tuple arg; THIS is two separate isinstance calls
    joined by `or`
  - Finding 339 (isinstance elif exhaustive) — that's sequential elif chains;
    THIS is a single compound condition
  - Finding 223 (Optional disjunctive tag) — that's about Optional[T] annotation;
    THIS is about runtime isinstance checks in boolean expressions

The key insight: the translator must COMPOSE narrowing assumptions from
boolean operators, not just extract them from single isinstance calls.
"""
from dataclasses import dataclass
from typing import Optional


@dataclass
class Result:
    value: int
    message: str


def process_numeric(x: object) -> int:
    """Process value that could be int or bool (bool is int subclass).
    
    CPython: isinstance(True, int) is True, so bool values enter this branch
    Model: if narrowing only emits isfrom_int, from_bool values may be rejected
    """
    if isinstance(x, int):
        # CPython: x is int (includes bool)
        # Model: assume(isfrom_int(x)) — but from_bool(True) fails this check!
        # This is finding 148/323 again, but in the context of OR conditions below
        return x + 0
    return -1


def classify_or_condition(value: object) -> str:
    """Classify using OR of isinstance checks.
    
    CPython: enters branch if value is int OR str
    Model risk: narrowing only captures one type, not the disjunction
    """
    if isinstance(value, int) or isinstance(value, str):
        # CPython: value is definitely int or str here
        # Model must emit: assume(isfrom_int(value) || isfrom_str(value))
        # If only one assume emitted, the other type causes assertion failure
        if isinstance(value, int):
            return "integer"
        else:
            return "string"
    return "other"


def safe_length_or_value(x: object) -> int:
    """Use OR isinstance to handle multiple types uniformly.
    
    CPython: if x is str or list, len(x) is valid
    Model: needs disjunctive narrowing to prove len() is safe
    """
    if isinstance(x, str) or isinstance(x, list):
        # CPython: x is str or list — len() valid for both
        # Model: assume(isfrom_str(x) || isfrom_ListAny(x))
        # Without disjunction, len(x) may fail tag check
        return len(x)
    return 0


def narrowing_with_and_not(x: object) -> str:
    """Narrowing via negated isinstance with and.
    
    `not isinstance(x, int) and not isinstance(x, str)` means
    x is NEITHER int nor str. The else branch means x IS int or str.
    """
    if not isinstance(x, int) and not isinstance(x, str):
        return "neither"
    else:
        # CPython: x is int or str (De Morgan's of the condition)
        # Model: must emit assume(isfrom_int(x) || isfrom_str(x))
        # This is the NEGATION of the if-condition, which requires
        # De Morgan's law: !(A && B) = !A || !B applied to narrowing
        if isinstance(x, int):
            return "int_path"
        return "str_path"


def main() -> None:
    # Test classify_or_condition
    r1: str = classify_or_condition(42)
    assert r1 == "integer"

    r2: str = classify_or_condition("hello")
    assert r2 == "string"

    r3: str = classify_or_condition(3.14)
    assert r3 == "other"

    # Test safe_length_or_value
    n1: int = safe_length_or_value("hello")
    assert n1 == 5

    n2: int = safe_length_or_value([1, 2, 3])
    assert n2 == 3

    n3: int = safe_length_or_value(42)
    assert n3 == 0

    # Test narrowing_with_and_not
    s1: str = narrowing_with_and_not(42)
    assert s1 == "int_path"

    s2: str = narrowing_with_and_not("hi")
    assert s2 == "str_path"

    s3: str = narrowing_with_and_not(3.14)
    assert s3 == "neither"

    print("all assertions passed")


main()

# Repeated field access after narrowing — second `DictStrAny_get` is
# unconstrained; narrowing from `if obj.field is not None:` doesn't propagate
# to subsequent reads of same field
"""
REPEATED FIELD ACCESS AFTER NARROWING — SECOND READ NOT NARROWED

DIVERGENCE:
  CPython:  `if obj.field is not None: x = obj.field + 1` works.
            The field value doesn't change between the check and the use.
  Model:    Each `obj.field` access translates to `DictStrAny_get(attrs, "field")`.
            The narrowing from the condition applies to the FIRST read.
            A SECOND read of the same field is a fresh uninterpreted call —
            the solver doesn't know it returns the same value.

This is distinct from finding 149 (which covers Optional field construction)
and finding 137 (which covers narrowing persistence through a branch for
LOCAL VARIABLES). This finding is about FIELD ACCESS specifically.

ROOT CAUSE: In the value-semantics model, `obj.field` is translated as
`DictStrAny_get(obj.instance_attributes, "field")`. Without a frame axiom
stating "if attrs hasn't changed, get returns the same value", two reads
of the same field are independent to the solver.

The narrowing `assume(!isfrom_None(DictStrAny_get(attrs, "field")))` only
constrains ONE specific term. A second `DictStrAny_get(attrs, "field")`
is a syntactically different term that the solver treats as unconstrained.
"""
from dataclasses import dataclass
from typing import Optional


@dataclass
class Config:
    host: str
    port: Optional[int]
    timeout: Optional[int]


def use_field_twice_after_check(c: Config) -> int:
    """Read field twice after narrowing — second read must also be narrowed."""
    if c.port is not None:
        # First use: narrowed by condition
        base: int = c.port
        # Second use: SAME field, should still be narrowed
        # Model: second DictStrAny_get is unconstrained — may be None!
        doubled: int = c.port * 2
        return base + doubled
    return -1


def field_in_arithmetic_chain(c: Config) -> int:
    """Multiple uses of narrowed field in one expression."""
    if c.port is not None and c.timeout is not None:
        # Both fields narrowed. But each access is independent in model.
        # CPython: c.port and c.timeout are stable ints
        # Model: each DictStrAny_get may return different values
        return c.port + c.timeout + c.port * c.timeout
    return 0


def field_passed_to_function(c: Config) -> int:
    """Narrowed field passed as argument — must retain narrowed type."""
    if c.port is not None:
        # c.port is int here
        result: int = double(c.port)
        # c.port is STILL int (no mutation happened)
        return result + c.port
    return -1


def double(x: int) -> int:
    return x * 2


def field_in_comparison_after_narrow(c: Config) -> bool:
    """Use narrowed field in comparison."""
    if c.port is not None:
        # c.port is int, can compare with int
        return c.port > 1024
    return False


def main() -> None:
    c1: Config = Config(host="localhost", port=8080, timeout=30)
    c2: Config = Config(host="localhost", port=None, timeout=None)

    # Test 1: field used twice
    assert use_field_twice_after_check(c1) == 8080 + 16160  # 24240
    assert use_field_twice_after_check(c2) == -1

    # Test 2: arithmetic chain
    assert field_in_arithmetic_chain(c1) == 8080 + 30 + 8080 * 30  # 250510
    assert field_in_arithmetic_chain(c2) == 0

    # Test 3: passed to function
    assert field_passed_to_function(c1) == 16160 + 8080  # 24240
    assert field_passed_to_function(c2) == -1

    # Test 4: comparison
    assert field_in_comparison_after_narrow(c1) == True
    assert field_in_comparison_after_narrow(c2) == False

    print("all passed")


main()

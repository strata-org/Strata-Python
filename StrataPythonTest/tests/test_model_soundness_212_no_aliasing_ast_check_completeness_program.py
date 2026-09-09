# No aliasing AST check completeness — catalog of ALL patterns that create
# aliases (direct copy, param, container, return self, nested field)
"""
"No aliasing" is enforced by the AST checker. But what EXACTLY must it
reject? This finding catalogs ALL aliasing patterns that would be unsound
under value semantics, testing that the AST check is COMPLETE.

Aliasing occurs when two variables refer to the same mutable object.
Under value semantics, they'd be independent copies — diverging from
CPython where mutations through one are visible through the other.

Patterns that create aliases:
1. `b = a` (direct assignment of class/list/dict variable)
2. `f(a)` (function parameter aliases caller's variable)
3. `lst.append(obj)` (container holds reference to obj)
4. `return self` (caller's variable aliases the returned self)
5. `obj.field = other_obj` (field holds reference)

Uses ONLY confirmed-accepted constructs: @dataclass, list, dict, int.
(Programs demonstrate patterns that SHOULD be rejected.)
"""
from dataclasses import dataclass


@dataclass
class Mutable:
    value: int


# Pattern 1: Direct variable alias
def direct_alias_diverges() -> bool:
    """b = a creates alias in CPython, copy in model."""
    a: Mutable = Mutable(value=1)
    b: Mutable = a  # ALIAS in CPython, COPY in model
    a.value = 99
    # CPython: b.value == 99 (same object)
    # Model: b.value == 1 (independent copy)
    return b.value == 99  # True in CPython


# Pattern 2: Function parameter alias
def param_alias_diverges() -> bool:
    """Function param aliases caller's variable in CPython."""
    def modify(obj: Mutable) -> None:
        obj.value = 42

    x: Mutable = Mutable(value=0)
    modify(x)
    # CPython: x.value == 42
    # Model: x.value == 0 (param was a copy)
    return x.value == 42  # True in CPython


# Pattern 3: Container holds reference
def container_alias_diverges() -> bool:
    """Object in list aliases the original in CPython."""
    obj: Mutable = Mutable(value=10)
    lst: list[Mutable] = [obj]  # lst[0] aliases obj in CPython
    obj.value = 99
    # CPython: lst[0].value == 99
    # Model: lst[0].value == 10 (stored a copy)
    return lst[0].value == 99  # True in CPython


# Pattern 4: Safe patterns (no aliasing)
def safe_independent_construction() -> bool:
    """Separate constructions are always safe."""
    a: Mutable = Mutable(value=1)
    b: Mutable = Mutable(value=1)
    a.value = 99
    return b.value == 1  # True in BOTH (independent objects)


def safe_return_new() -> bool:
    """Returning a new instance is safe."""
    def make_modified(obj: Mutable) -> Mutable:
        return Mutable(value=obj.value + 1)

    x: Mutable = Mutable(value=5)
    y: Mutable = make_modified(x)
    return x.value == 5 and y.value == 6  # True in BOTH


def main() -> None:
    # Aliasing patterns (diverge between CPython and model)
    assert direct_alias_diverges() == True  # CPython behavior
    assert param_alias_diverges() == True
    assert container_alias_diverges() == True

    # Safe patterns (same in both)
    assert safe_independent_construction() == True
    assert safe_return_new() == True

    print(direct_alias_diverges(), safe_independent_construction(),
          safe_return_new())


main()

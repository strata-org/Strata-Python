# Nested call `f(g(x))` — return type of g must be assumed at call site to
# prove f's param assertion; needs inter-procedural contract
"""
NESTED FUNCTION CALL — RETURN TYPE OF INNER MUST SATISFY PARAM TYPE OF OUTER

CPython: f(g(x)) — g returns int, f expects int. Type flows through.

Model:   g(x) returns from_int(result).
         f(from_int(result)) — f's parameter has tag assertion isfrom_int.
         The caller must ASSUME g's return type to PROVE f's precondition.

         Without inter-procedural contracts (finding 225):
         - g's return value is unconstrained (Hole)
         - f's parameter assertion fails (can't prove isfrom_int(Hole))
         - Verifier reports false positive: "possible TypeError"

This tests the INTER-PROCEDURAL TYPE FLOW that the subset requires:
full annotations on all functions means the verifier should use
return-type annotations as assumptions at call sites.
"""


def double(x: int) -> int:
    return x * 2


def add_one(x: int) -> int:
    return x + 1


def negate(x: int) -> int:
    return -x


def nested_simple(x: int) -> int:
    """f(g(x)) — return type of g feeds into param type of f."""
    return add_one(double(x))


def deeply_nested(x: int) -> int:
    """f(g(h(x))) — three levels of nesting."""
    return negate(add_one(double(x)))


def nested_with_arithmetic(x: int) -> int:
    """f(g(x)) + h(x) — nested call result used in arithmetic."""
    return double(x) + add_one(x)


def nested_in_condition(x: int) -> bool:
    """Nested call result used in comparison."""
    return double(x) > add_one(x)


def chain_through_variable(x: int) -> int:
    """Same as nested but via intermediate variable."""
    a: int = double(x)
    b: int = add_one(a)
    c: int = negate(b)
    return c


def main() -> None:
    # Test 1: simple nesting
    assert nested_simple(3) == 7  # double(3)=6, add_one(6)=7

    # Test 2: deep nesting
    assert deeply_nested(3) == -7  # double(3)=6, add_one(6)=7, negate(7)=-7

    # Test 3: nested + arithmetic
    assert nested_with_arithmetic(3) == 10  # double(3)=6, add_one(3)=4, 6+4=10

    # Test 4: nested in condition
    assert nested_in_condition(3)  # double(3)=6 > add_one(3)=4

    # Test 5: chain through variables (equivalent to nesting)
    assert chain_through_variable(3) == -7

    print("all passed")


main()

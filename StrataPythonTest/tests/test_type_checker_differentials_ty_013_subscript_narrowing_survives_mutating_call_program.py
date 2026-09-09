# ty-unsoundness witness 013 — subscript-place narrowing survives a mutating call.
#
# ty verdict      : clean            (TY: clean via scripts/ty_check.py)
# CPython (3.14.3): TypeError         "unsupported operand type(s) for +: 'NoneType' and 'int'"
# mypy --strict   : clean            <-- SHARED mypy n ty hole (4th, after 006/cast, 011, 012)
#
# ty source site targeted:
#   repos/ruff/crates/ty_python_semantic/src/types/narrow.rs:1268-1276
#       CmpOp::IsNot => if rhs is a singleton (None): Some(rhs_ty.negate(db))  -> drops None
#   repos/ruff/crates/ty_python_semantic/src/types/narrow.rs:1297,1308,776
#       a Subscript expr IS a narrowing target/place; constraint keyed to the
#       ScopedPlaceId of place `d["k"]` (evaluate_simple_expr :1022-1040, expect_place :920).
#   No call-effect / alias invalidation: a `clear(d)` call creates no new binding of
#   place `d["k"]` in this scope, so the "not None" constraint on d["k"] survives the call.
#   (Distinct from 011: subscript PLACE + aliased container mutation, NOT name + `global`.)
#
# Routing: clear(d) reassigns d["k"]=None through the *same* dict object the caller passed;
# ty cannot see this (no heap/alias model), keeps d["k"]: int, trusts `-> int`, returns None.

def clear(d: dict[str, int | None]) -> None:
    d["k"] = None

def f(d: dict[str, int | None]) -> int:
    if d["k"] is not None:      # ty narrows place d["k"]: int|None -> int  (narrow.rs:1268-1276)
        clear(d)                # mutates d["k"] to None through the alias; ty does NOT invalidate
        return d["k"]           # ty: still `int` (clean against `-> int`); runtime value is None
    return 0

m: dict[str, int | None] = {"k": 5}
r = f(m)                        # r is None at runtime, `int` to ty
print(r + 1)                    # CPython: TypeError (NoneType + int)

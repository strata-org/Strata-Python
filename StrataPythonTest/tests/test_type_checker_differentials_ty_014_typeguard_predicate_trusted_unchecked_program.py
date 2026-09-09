# ty verdict     : clean            (TY-UNSOUND)
# CPython 3.14.3 : TypeError        ("can only concatenate str (not \"int\") to str")
# mypy --strict  : clean            (shared mypy ∩ ty hole — PEP 647 makes the body the author's job)
# ty source site : repos/ruff/crates/ty_python_semantic/src/types/narrow.rs:1822-1826
#                  Type::TypeGuard(type_guard) => NarrowingConstraint::replacement(type_guard.return_type(db))
#                  (return type lifted verbatim from the annotation at type_expression.rs:2185-2188;
#                   the predicate BODY is never checked to actually establish the type)
#
# Mechanism: a user-defined PEP 647 TypeGuard. ty narrows `x` to the guard's *declared*
# return type `int` on the strength of the `-> TypeGuard[int]` annotation alone. The body
# `return True` lies — it certifies nothing — but ty (and mypy) trust it by spec. The
# narrowed `int` is a concrete type, so `return x` is accepted by ordinary subtyping; this
# BYPASSES relation.rs:1093 entirely (no dynamic type is ever produced), exactly like the
# flow/narrowing door of findings 011/013 — but here the unsoundness is at the guard
# DEFINITION (trusting an unverified predicate), not flow-invalidation after the guard.

from typing import TypeGuard


def is_int(x: object) -> TypeGuard[int]:
    return True  # lies: claims every value is an int, certifies nothing


def f(x: object) -> int:
    if is_int(x):
        return x  # ty: x narrowed to `int` via TypeGuard -> ok against `-> int`
    return 0


f("hello") + 1  # CPython: f returns "hello" (a str); "hello" + 1 -> TypeError

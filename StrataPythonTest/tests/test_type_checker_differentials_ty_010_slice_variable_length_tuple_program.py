# ty-unsoundness witness 010 — slice into a variable-length tuple yields `Todo`
#
# ty verdict      : clean
# CPython (3.14.3): AttributeError  ('tuple' object has no attribute 'upper')
# mypy            : error [return-value]  (BOTH --strict AND default mode catch it)
# Monty runtime   : AttributeError (agrees with CPython)
#
# Source site targeted:
#   repos/ruff/crates/ty_python_semantic/src/types/subscript.rs:613
#     TupleSpec::Variable(_) => Ok(todo_type!("slice into variable-length tuple"))
#   laundered through:
#   repos/ruff/crates/ty_python_semantic/src/types/relation.rs:1093
#     (Type::Dynamic(_dynamic), _) => ... Assignability => true
#
# Mechanism: `t[1:]` where `t: tuple[int, ...]` (a *variable-length* / homogeneous
# tuple, TupleSpec::Variable) has its subscript result minted as Type::Todo — a
# Type::Dynamic. The `-> str` return then checks "is Todo assignable to str?" at
# relation.rs:1093, which answers `true` for any dynamic type. ty accepts. At
# runtime the slice is a `tuple`, and `.upper()` on it raises AttributeError.
#
# This is NOT the 001-009 Unknown-laundering family: the dynamic type here is
# `Todo`, minted by a specific incomplete-feature site, and the gap survives even
# fully-annotated code that mypy (default mode, no strict flag) rejects outright.

def f(t: tuple[int, ...]) -> str:
    return t[1:]            # slice of a variable-length tuple -> Type::Todo

f((1, 2, 3)).upper()        # ty thinks `str`; runtime tuple has no .upper()

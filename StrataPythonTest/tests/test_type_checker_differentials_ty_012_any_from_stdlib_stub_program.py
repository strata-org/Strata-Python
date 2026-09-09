# Witness: explicit `Any` from a typeshed stdlib stub launders into a concrete
# `int` annotation, then crashes at use.
#
#   ty      : clean
#   CPython : TypeError ("can only concatenate str ... to str" — x is the str "nope")
#   mypy --strict : clean  (shared mypy n ty hole)
#
# Source site targeted:
#   - json.loads(...) -> Any
#       repos/monty/crates/monty-typeshed/vendor/typeshed/stdlib/json/__init__.pyi:49
#     mints Type::Dynamic(DynamicType::Any) -- the EXPLICIT `Any`, the third
#     DynamicType member (001-009 reached Unknown; 010 reached Todo; this is Any).
#   - assignment `x: int = <Any>` checks Any-assignable-to-int at
#       repos/ruff/crates/ty_python_semantic/src/types/relation.rs:1093
#       (Type::Dynamic(_dynamic), _) => ... Assignability => true
#     so the assignment is accepted and x is thereafter treated as a concrete int.
import json

x: int = json.loads('"nope"')   # runtime value is the str "nope"
print(x + 1)                    # ty: int + 1 (clean); CPython: str + int -> TypeError

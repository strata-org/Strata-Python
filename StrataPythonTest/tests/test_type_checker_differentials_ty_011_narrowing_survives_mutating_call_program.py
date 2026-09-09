# ty-unsoundness witness 011 — narrowing survives a call that mutates the narrowed binding
#
# ty verdict      : clean
# CPython (3.14.3): TypeError  (unsupported operand type(s) for +: 'NoneType' and 'int')
# mypy --strict   : clean  (SHARED mypy ∩ ty hole — like 006/cast)
# mypy (default)  : clean
# Monty runtime   : TypeError (agrees with CPython)
#
# Source site targeted (a NARROWING-model gap, NOT dynamic laundering):
#   repos/ruff/crates/ty_python_semantic/src/types/narrow.rs:1269-1277
#     ast::CmpOp::IsNot => { if rhs_ty.is_singleton(..) { Some(rhs_ty.negate(..)) } ... }
#       -> `x is not None` mints a negative-None constraint; declared Optional[int]
#          narrows to the CONCRETE type `int`.
#   repos/ruff/crates/ty_python_semantic/src/types/narrow.rs:744-791
#     narrowing constraints are evaluated syntactically and attached to the symbol's
#     reaching BINDING in the semantic index. There is no call-effect invalidation:
#     a function call between the guard and the use is not a binding event for the
#     (global) name in the caller's scope, so the narrowing is never widened back.
#
# NOTE: the narrowed type here is concrete `int`, so this does NOT route through the
# Type::Dynamic branch relation.rs:1093 that 001-010 rely on. It is a distinct,
# flow-sensitivity unsoundness: ty's narrowing assumes the only way a name's type
# changes between guard and use is a *visible* assignment in the same scope.
#
# Mechanism: `if x is not None:` narrows global `x: Optional[int]` to `int`. The call
# `clear()` does `global x; x = None`, invisible to the caller's use-def chain. ty keeps
# the narrowing, so `x + 1` is accepted as `int + int`. At runtime x is None -> TypeError.

from typing import Optional

x: Optional[int] = 1

def clear() -> None:
    global x
    x = None

if x is not None:        # ty narrows x: Optional[int] -> int  (narrow.rs:1269-1277)
    clear()              # mutates global x to None — NOT a binding event in this scope
    print(x + 1)         # ty: int + int (accepted); runtime: None + 1 -> TypeError

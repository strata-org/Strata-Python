# ty verdict   : clean            (scripts/ty_check.py -> TY: clean)
# CPython      : ValueError: not enough values to unpack (expected 2, got 1)
# mypy --strict: clean            (Success: no issues found) -> 5th shared mypy n ty hole
# CPython pin  : v3.14.3
#
# ty source site targeted (NOT relation.rs:1093 / NOT a todo_type! site):
#   repos/ruff/crates/ty_python_semantic/src/types/tuple.rs:1037-1054
#     VariableLengthTuple::resize, the `TupleLength::Fixed(new_length)` arm:
#       let Some(variable_count) = new_length.checked_sub(self.len().minimum()) else {
#           return Err(ResizeTupleError::TooManyValues);
#       };
#       Ok(Tuple::Fixed(...))   // <-- succeeds for ANY new_length >= minimum
#   For `tuple[int, ...]`  minimum() == prefix+suffix == 0  (tuple.rs:68), so
#   resizing to any fixed target arity N>=0 returns Ok -> unpack accepted silently.
#   Contrast: FixedLengthTuple::resize (tuple.rs:667) errors TooFew/TooManyValues
#   on any length mismatch, which is why ty DOES catch `a,b,c = (tuple[int,int])`.
#   Driver: unpacker.rs:218-256 (TupleUnpacker::unpack_tuple).
#
# This is a CARDINALITY/ARITY unsoundness, a door distinct from 001-014:
#   - the unpacked elements are correctly typed `int` (NOT a dynamic type) -- a
#     follow-on `c: str = a` is in fact REJECTED by ty (invalid-assignment), proving
#     no Unknown/Todo/Any laundering is involved here;
#   - ty simply models `tuple[int, ...]` as having unbounded length, so it cannot
#     prove the runtime length (1) differs from the target arity (2).

def make() -> tuple[int, ...]:
    return (1,)            # runtime length 1

a, b = make()              # ty: clean (variable-length resize accepts arity 2)
                           # CPython: ValueError (expected 2, got 1)
print(a + b)

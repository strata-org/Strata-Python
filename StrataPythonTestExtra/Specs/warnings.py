from typing import Any, Dict, List, NotRequired, TypedDict, Unpack

# Unsupported __init__ assignment value (not self._ClassName() pattern)
class BadInit:
    def __init__(self):
        self.name = "hello"

# Skipped Assign in function body
def skipped_assign(**kw: int) -> None:
    x = kw["a"]
    assert x >= 1, 'x >= 1'

LoopRequest = TypedDict('LoopRequest', {
    'Items': NotRequired[List[str]],
    'Data': NotRequired[Dict[str, str]],
})

# Legacy generated PySpecs still use statement-form universal quantifiers.
def for_loop_supported(**kw: Unpack[LoopRequest]) -> None:
    for item in kw["Items"]:
        assert len(item) >= 1, 'Expected len(item) >= 1'

# A benign skipped statement must not discard assertions from a legacy loop.
def for_loop_with_docstring(**kw: Unpack[LoopRequest]) -> None:
    for item in kw["Items"]:
        """each item is validated"""
        assert len(item) >= 1, 'Expected len(item) >= 1'

# Bare dict iteration is key iteration, matching Python semantics.
def bare_dict_supported(**kw: Unpack[LoopRequest]) -> None:
    assert all(len(k) >= 1 for k in kw["Data"]), 'all keys non-empty'

# Tuple targets over d.items() are valid for both all() and any().
def exists_items_supported(**kw: Unpack[LoopRequest]) -> None:
    assert any(len(k) >= 1 for k, v in kw["Data"].items()), 'some key non-empty'

# Skipped Expr in function body (non-ellipsis expression statement)
def skipped_expr(**kw: int) -> None:
    kw["a"]

# Equality whose right-hand side is unsupported: the warning must be emitted
# once, not duplicated by the transCompare .Eq fall-through.
def eq_bad_rhs(**kw: int) -> None:
    assert kw["a"] == kw["a"].bit_length(), 'eq bad rhs'

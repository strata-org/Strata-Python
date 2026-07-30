# PySpec fixture for the dispatch end-to-end tests (AnalyzeLaurelTest.lean).
#
# Each method's `assert` statements are extracted as PySpec preconditions of
# that method. The sibling `test_*.py` scripts then call these methods through
# `servicelib.connect("storage")` with concrete arguments, and the test
# harness verifies the resulting SMT obligations:
#   - `test_*_pass.py` calls satisfy the precondition, so the quantified
#     obligation must be proven;
#   - `test_*_violation.py` calls violate it (e.g. a list containing an empty
#     string passed to `require_all_nonempty`), so the obligation must fail.
#
# The `require_*` methods below each pin one quantifier domain: list elements,
# dict items/keys/values, a guarded (`if`) quantifier, and existentials over a
# list and over dict items.
from typing import TypedDict, Required, NotRequired, Unpack, List, Dict

PutItemRequest = TypedDict('PutItemRequest', {
    'Bucket': Required[str],
    'Key': Required[str],
    'Data': Required[str],
})

GetItemRequest = TypedDict('GetItemRequest', {
    'Bucket': Required[str],
    'Key': Required[str],
})

GetItemResponse = TypedDict('GetItemResponse', {
    'Data': NotRequired[str],
    'Found': NotRequired[bool],
})

ListItemsRequest = TypedDict('ListItemsRequest', {
    'Bucket': Required[str],
    'MaxResults': NotRequired[int],
    'NextToken': NotRequired[str],
})

@exhaustive
class Storage:
    def put_item(self, **kwargs: Unpack[PutItemRequest]) -> None:
        assert len(kwargs["Bucket"]) >= 1, "Bucket must not be empty"
        assert compile(r'^[a-z0-9-]+$').search(kwargs["Bucket"]) is not None, "Bucket must match ^[a-z0-9-]+$"
        assert len(kwargs["Key"]) >= 1, "Key must not be empty"
    def get_item(self, **kwargs: Unpack[GetItemRequest]) -> GetItemResponse:
        assert len(kwargs["Bucket"]) >= 1, "Bucket must not be empty"
        assert len(kwargs["Key"]) >= 1, "Key must not be empty"
    def delete_item(self, Bucket: str, Key: str) -> None:
        ...
    def list_items(self, **kwargs: Unpack[ListItemsRequest]) -> None:
        ...
    def require_all_nonempty(self, Keys: List[str]) -> None:
        assert all(len(k) >= 1 for k in Keys), "each key must be non-empty"
    def require_map_nonempty(self, Items: Dict[str, str]) -> None:
        assert all(len(k) >= 1 for k, v in Items.items()), "each key must be non-empty"
        assert all(len(v) >= 1 for k, v in Items.items()), "each value must be non-empty"
    def require_others_nonempty(self, Keys: List[str], Sentinel: str) -> None:
        assert all(len(k) >= 1 for k in Keys if k != Sentinel), "each key other than the sentinel must be non-empty"
    def require_some_match(self, Keys: List[str], Needle: str) -> None:
        assert any(k == Needle for k in Keys), "at least one key must match the needle"
    # Existential over dict items: the value binder is inlined as a `d[k]`
    # lookup, so this pins that the value inlining composes with the
    # existential's conjunction the same way it does under `all(...)`.
    def require_some_value_match(self, Items: Dict[str, str], Needle: str) -> None:
        assert any(v == Needle for k, v in Items.items()), "at least one value must match the needle"
    def require_keys_nonempty(self, Items: Dict[str, str]) -> None:
        assert all(len(k) >= 1 for k in Items.keys()), "each key must be non-empty"
    def require_values_nonempty(self, Items: Dict[str, str]) -> None:
        assert all(len(v) >= 1 for v in Items.values()), "each value must be non-empty"
    # The binder deliberately shadows its own collection: the generated
    # quantifier must keep reading the argument `Keys`, not the binder.
    def require_shadowed_nonempty(self, Keys: List[str]) -> None:
        assert all(len(Keys) >= 1 for Keys in Keys), "each shadowed key must be non-empty"
    # Nested quantifier whose inner binder `k` shadows the outer dict key `k`;
    # the inner domain `v` is inlined as a lookup on the *outer* key.
    def require_groups_nonempty(self, Groups: Dict[str, List[str]]) -> None:
        assert all(all(len(k) >= 1 for k in v) for k, v in Groups.items()), "each group member must be non-empty"

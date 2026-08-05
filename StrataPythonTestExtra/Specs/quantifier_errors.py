from typing import Dict, List

# Unsupported iterable type.
def any_over_text(Text: str) -> None:
    assert any(len(c) >= 1 for c in Text), 'any over text'

# A string literal currently lowers to a diagnostic-free placeholder; it must
# still be rejected as an iterable rather than reaching domain selection.
def any_over_literal() -> None:
    assert any(len(c) >= 1 for c in "abc"), 'any over literal'

# Wrong arity.
def any_wrong_arity(Items: List[str]) -> None:
    assert any(Items, Items), 'any wrong arity'

# Non-generator argument.
def any_not_generator(Items: List[str]) -> None:
    assert any(Items), 'any non-generator'

# Multiple for clauses.
def any_multi_for(Items: List[str]) -> None:
    assert any(len(x) >= 1 for x in Items for y in Items), 'any multi for'

# Binder/domain mismatches.
def any_tuple_target(Items: List[str]) -> None:
    assert any(len(a) >= 1 for (a, b) in Items), 'any tuple target'

def any_single_over_items(Data: Dict[str, str]) -> None:
    assert any(len(kv) >= 1 for kv in Data.items()), 'any over items'

# Multiple guards.
def all_multi_if(Items: List[str]) -> None:
    assert all(len(x) >= 1 for x in Items if len(x) > 0 if x != ""), 'all multi if'

# The Laurel dict model only supports string keys.
def any_non_string_dict(Data: Dict[int, str]) -> None:
    assert any(len(v) >= 1 for v in Data.values()), 'integer-keyed dict'

# Unsupported expressions inside an otherwise valid quantifier must make the
# whole contract fail rather than dropping it.
def any_bad_body(Items: List[str]) -> None:
    assert any(x.bit_length() >= 1 for x in Items), 'bad body'

def any_placeholder_body(Items: List[str]) -> None:
    assert any("literal" for x in Items), 'placeholder body'

def all_bad_guard(Items: List[str]) -> None:
    assert all(len(x) >= 1 for x in Items if x.bit_length()), 'bad guard'

def all_placeholder_guard(Items: List[str]) -> None:
    assert all(len(x) >= 1 for x in Items if "literal"), 'placeholder guard'

# Statement-form quantifiers follow the same hard-error policy.
def for_over_text(Text: str) -> None:
    for c in Text:
        assert len(c) >= 1, 'for over text'

def for_over_literal() -> None:
    for c in "abc":
        assert len(c) >= 1, 'for over literal'

def for_placeholder_body(Items: List[str]) -> None:
    for x in Items:
        assert "literal", 'placeholder body'

def for_mixed_body(Items: List[str]) -> None:
    for x in Items:
        assert len(x) >= 1, 'valid assertion must be rolled back'
        assert "literal", 'placeholder makes the whole loop invalid'

def for_else(Items: List[str]) -> None:
    for x in Items:
        assert len(x) >= 1, 'for else'
    else:
        pass

# Nested Dict[int, _] inside an outer for: the inner loop's non-str-key
# warning uses .pySpecDroppedAssertion, so the outer quantifyBody detects
# the incomplete body and fires "loop body could not be fully translated".
def for_nested_int_dict(D: Dict[str, Dict[int, str]]) -> None:
    for k, v in D.items():
        assert len(k) >= 1, 'outer precondition'
        for i in v:
            assert i >= 0, 'inner precondition on int key'

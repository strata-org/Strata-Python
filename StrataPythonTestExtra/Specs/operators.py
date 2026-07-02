from typing import List, TypedDict, Unpack

OpRequest = TypedDict('OpRequest', {
    'a': int,
    'b': int,
    'c': int,
    'score': float,
    'items': List[int],
    'flag1': bool,
    'flag2': bool,
})


def arithmetic(**kw: Unpack[OpRequest]) -> None:
    assert kw["a"] + kw["b"] >= kw["c"], 'add in ge'
    assert kw["a"] - kw["b"] >= kw["c"], 'sub in ge'
    assert kw["a"] * kw["b"] >= kw["c"], 'mul in ge'
    assert kw["a"] // kw["b"] >= kw["c"], 'floordiv in ge'
    assert kw["a"] % kw["b"] >= kw["c"], 'mod in ge'
    assert kw["a"] ** kw["b"] >= kw["c"], 'pow in ge'
    assert -kw["a"] >= kw["c"], 'neg in ge'


def comparisons(**kw: Unpack[OpRequest]) -> None:
    assert kw["a"] > kw["b"], 'gt'
    assert kw["a"] < kw["b"], 'lt'
    assert kw["a"] != kw["b"], 'ne'
    assert kw["a"] == 5, 'eq int'
    assert kw["a"] in kw["items"], 'isin'
    assert kw["a"] not in kw["items"], 'notin'
    assert kw["a"] >= 1, 'int ge'
    assert kw["a"] <= 10, 'int le'
    assert kw["score"] >= 0.0, 'float ge'
    assert kw["score"] <= 1.0, 'float le'


def identity(**kw: Unpack[OpRequest]) -> None:
    assert kw["a"] is None, 'is none'
    assert kw["a"] is not None, 'is not none'


def boolean(**kw: Unpack[OpRequest]) -> None:
    assert kw["flag1"] and kw["flag2"], 'and'
    assert kw["flag1"] or kw["flag2"], 'or'
    assert not kw["flag1"], 'not'

from typing import NotRequired, Required, TypedDict

# Without total=: each member takes its wrapper, and a bare type is required.
Plain = TypedDict('Plain', {
    'bare': int,
    'req': Required[int],
    'opt': NotRequired[int],
})

# total=True: a NotRequired member is still optional.
TotalTrue = TypedDict('TotalTrue', {
    'bare': int,
    'req': Required[int],
    'opt': NotRequired[int],
    'quoted': NotRequired['int'],
}, total=True)

# total=False: a Required member is still required; a bare type is optional.
TotalFalse = TypedDict('TotalFalse', {
    'bare': int,
    'req': Required[int],
    'opt': NotRequired[int],
}, total=False)

# A name bound to a wrapper reads as the wrapper.
Opt = NotRequired[int]
Named = TypedDict('Named', {
    'opt': Opt,
    'bare': int,
})

def f(a: Plain, b: TotalTrue, c: TotalFalse, d: Named) -> None:
    ...

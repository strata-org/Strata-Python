# The schema of the return types of overloads (docs/PythonToDyn.md §12.1 and §12.3): a stub's
# clauses apply only to the calls that select it, and the base's to every call.
from typing import List, Literal, NotRequired, Required, TypedDict, overload

A = TypedDict('A', {
    'Name': Required[str],
})

B = TypedDict('B', {
    'Ids': NotRequired[List[int]],
})

Base = TypedDict('Base', {
    'Kind': Required[str],
    'Ids': NotRequired[List[int]],
})

@overload
def fetch(kind: Literal["a"]) -> A:
    ...

@overload
def fetch(kind: Literal["b"]) -> B:
    ...

def fetch(kind: str) -> Base:
    ...

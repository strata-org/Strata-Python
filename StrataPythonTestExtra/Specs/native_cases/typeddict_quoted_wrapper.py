from typing import NotRequired, TypedDict

Out = TypedDict('Out', {
    'b': 'NotRequired[int]',
}, total=True)

def f() -> Out:
    ...

from typing import NotRequired, Required, TypedDict

Out = TypedDict('Out', {
    'a': Required[str],
    'a': NotRequired[int],
})

def f() -> Out:
    ...

from typing import Annotated, NotRequired, TypedDict

Out = TypedDict('Out', {
    'b': Annotated[NotRequired[int], 'note'],
}, total=True)

def f() -> Out:
    ...

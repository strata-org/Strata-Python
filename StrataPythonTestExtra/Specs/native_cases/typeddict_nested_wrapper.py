from typing import List, NotRequired, Optional, Required, TypedDict, Union

A = TypedDict('A', {'a': Union[NotRequired[int], NotRequired[int]]})
B = TypedDict('B', {'a': Optional[NotRequired[int]]}, total=False)
C = TypedDict('C', {'a': NotRequired[Required[int]]}, total=False)
D = TypedDict('D', {'a': Required[NotRequired[int]]}, total=False)
E = TypedDict('E', {'a': List[NotRequired[int]]})
F = TypedDict('F', {'a': NotRequired[int] | NotRequired[int]})
U = Union[NotRequired[int], None]

def f(x: NotRequired[int]) -> None:
    ...

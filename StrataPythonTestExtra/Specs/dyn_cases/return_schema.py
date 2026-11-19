# The schema of model return types (docs/PythonToDyn.md §12.3, Return schema): one clause per
# member, element or entries of the result, for each form of type and each kind of function.
from typing import Any, BinaryIO, Dict, List, Literal, Mapping, NotRequired, Optional, Required, Sequence, TypedDict, Union, overload

Leaf = TypedDict('Leaf', {
    'S': Required[str],
    'I': NotRequired[int],
    'F': NotRequired[float],
    'B': NotRequired[bool],
    'Y': NotRequired[bytes],
    'N': NotRequired[None],
    'A': NotRequired[Any],
    'R': Required[Any],
    'E': NotRequired[Literal["ACTIVE", "DISABLED"]],
    'K': NotRequired[Literal[1, 2]],
    'from': NotRequired[str],
})

Out = TypedDict('Out', {
    'Leaf': Required['Leaf'],
    'Items': NotRequired[List['Leaf']],
    'Names': NotRequired[Sequence[str]],
    'Tags': NotRequired[Dict[str, str]],
    'Doc': NotRequired[Dict[str, Any]],
    'Counts': NotRequired[Dict[Any, int]],
    'Blob': NotRequired[Dict[Any, Any]],
    'ByName': NotRequired[Mapping[str, 'Leaf']],
    'Maybe': NotRequired[Optional['Leaf']],
    'Sparse': NotRequired[List[Optional[str]]],
    'Either': NotRequired[Union[List[int], Dict[str, int]]],
    'Grid': NotRequired[List[List[str]]],
    'Rec': NotRequired['Value'],
    'Later': NotRequired['LaterList'],
    'Tree': NotRequired['Tree'],
    'Two': NotRequired[Union['Leaf', 'Other']],
    'Opt': NotRequired['MaybeLeaf'],
    'OptOpt': NotRequired[Optional['MaybeLeaf']],
    'Owner': NotRequired['Client'],
    'Owners': NotRequired[List['Client']],
    'Raw': NotRequired[BinaryIO],
    'Raws': NotRequired[List[BinaryIO]],
})

Value = TypedDict('Value', {
    'S': NotRequired[str],
    'M': NotRequired[Dict[str, 'Value']],
    'L': NotRequired[List['Value']],
})

Other = TypedDict('Other', {
    'X': Required[int],
})

LaterList = List['Leaf']
Tree = List['Tree']
MaybeLeaf = Optional[Leaf]
Ping = List['Pong']
Pong = List['Ping']

Void = TypedDict('Void', {})

# total=True with a NotRequired member: only Kept is required.
Totals = TypedDict('Totals', {
    'Kept': int,
    'Maybe': NotRequired[int],
}, total=True)

def every_kind() -> Out:
    ...

def a_list() -> List['Leaf']:
    ...

def a_dict() -> Dict[str, 'Leaf']:
    ...

def totals() -> Totals:
    ...

def optional() -> Optional['Leaf']:
    ...

def void() -> Void:
    ...

def ping() -> Ping:
    ...

def nothing() -> None:
    ...

def anything() -> Any:
    ...

class Client:
    def get(self) -> Out:
        ...

    def __add__(self, other: int) -> Leaf:
        ...

    @overload
    def pick(self, kind: Literal["a"]) -> Leaf:
        ...

    @overload
    def pick(self, kind: Literal["b"]) -> Other:
        ...

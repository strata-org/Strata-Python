# More of typing: nested aliases, unions of both kinds, isinstance, and the attributes of aliases.
from typing import List, Dict, Optional, Union, Any, Tuple
print(Optional[List[Any]], Optional[Dict[str, Any]], Optional[int] | str, List[int] | None)
print((int | None) == Optional[int], Optional[int] == (int | None), List[int] == list[int])
print({int | str: 1}[Union[int, str]], {Union[int, str]: 2}[str | int], {Any: 3}[Any])
print(isinstance(1, Optional[int]), isinstance("x", Optional[int]), isinstance([], List))
print(List[int].append is list.append, List[int].__name__, List.__name__, Optional.__name__)
print(List[int].__origin__, Dict[str, int].__args__, Tuple[()].__args__, List.__origin__)
print(Union[int, str].__module__, Optional[int].__parameters__, Union[int, Union[str, int]])
print(Optional[Optional[int]], Union[int, None, str], Union[None, int])
print(type(List), type(List[int]), type(Optional), type(Optional[int]), type(Any))
for bad in (lambda: List[int](), lambda: Optional(), lambda: Union[int, str](), lambda: Optional[1, 2],
            lambda: Optional[Optional]):
    try:
        bad()
    except TypeError as e:
        print("TypeError:", e)
try:
    class C(Optional):
        pass
except TypeError as e:
    print("TypeError:", e)
try:
    List[int].foo
except AttributeError as e:
    print("AttributeError:", e)
# The issubclass built-in is the library's.
print(issubclass(int, Optional[int]), issubclass(bool, Union[str, int]))

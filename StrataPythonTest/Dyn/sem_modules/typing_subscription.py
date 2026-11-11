# Subscription of typing's aliases and special forms.
from typing import List, Dict, Set, Tuple, Optional, Union, Any
print(List[int], Dict[str, Any], Set[int], Tuple[int, str], Tuple[()], Tuple[int, ...])
print(Optional[int], Union[int, str], Union[int], Optional[None], Union[int, None])
print(Union[int, str] == Union[str, int], Optional[int] == Union[int, None], List[1])
print(Optional[int] | str, List[int] | None, int | Optional[str])
print((int | None) == Optional[int], list[int] == List[int])
print(List[int].__origin__, List[int].__args__, Optional[int].__args__)
print(isinstance([], List))
for bad in (lambda: List[int, str], lambda: Dict[str], lambda: Optional[(1, 2)], lambda: Union[()]):
    try:
        bad()
    except TypeError as e:
        print("TypeError:", e)
try:
    List[int]()
except TypeError as e:
    print("TypeError:", e)
try:
    isinstance([], List[int])
except TypeError as e:
    print("TypeError:", e)
try:
    iter(Optional)
except TypeError as e:
    print("TypeError:", e)

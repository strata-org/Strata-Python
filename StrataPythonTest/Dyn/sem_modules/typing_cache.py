# typing caches subscriptions: 128 entries per cache, least recently used first out.
from typing import Any, Dict, List, Optional, Tuple, Union
a = List[int]
print(a is List[int], List[True] is List[1], Tuple[int, ...] is Tuple[int, ...])
print(Optional[list[int]] is Optional[list[int]], Union[int, None] is Optional[int])
b = List[int | str]
print(List[Union[int, str]] is b, List["Node"] is List["Node"], List[Optional["N"]] is List[Optional["N"]])
# Keys that are == but built differently hit; keys in another order miss.
print(List[str | int] is List[Union[int, str]], Union[int, str] is Union[str, int], Union[int, str] == Union[str, int])
# A hit makes List[int] the most recent entry; it survives 127 other entries, but not 128.
print(List[int] is a)
for i in range(127):
    Dict[i, i]
print("after 127 others:", a is List[int])
for i in range(128):
    Dict[i, -i]
print("after 128 others:", a is List[int])

# Keys whose class leaves come in another order: equal keys still hit, and keys that are not ==
# miss.
class LA: pass
class LB: pass
print(List[LA] is List[LA], List[LA] is List[LB], Dict[LA, LB] is Dict[LB, LA], Dict[LA, LB] is Dict[LA, LB])
print(List[Union[LA, LB]] is List[Union[LB, LA]], List[LA | LB] is List[Union[LB, LA]], List[Optional[LA]] is List[LA | None])
print(Tuple[LA, LA, LB] is Tuple[LA, LB, LB], Tuple[LA, LB, LA] is Tuple[LA, LB, LA], Tuple[LA, ...] is Tuple[LA, ...])
print(List[list[LA]] is List[list[LA]], List[dict[LA, LB]] is List[dict[LB, LA]], List[Any] is List[Any], List[List] is List[List])
print(Optional[LA] is Optional[LA], Union[LA, LB, int] is Union[LA, LB, int], Union[LA, LB, int] == Union[int, LB, LA])
print(List[Union[LA, LB, int]] is List[Union[int, LB, LA]], List[Tuple[LA, LB]] is List[Tuple[LB, LA]])

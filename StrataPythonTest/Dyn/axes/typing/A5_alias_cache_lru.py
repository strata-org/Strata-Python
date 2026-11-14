from typing import List, Dict, Set, Tuple, Optional, Union
first = List[int]
cs = [type('C%d' % i, (), {'__module__': '__main__'}) for i in range(128)]
for c in cs:
    Dict[c, int]
print(List[int] is first)
t = Tuple[int]
for c in cs:
    List[c]
print(Tuple[int] is t)
o = Optional[int]
for c in cs[:127]:
    Union[c, None]
print(Optional[int] is o, Union[int, None] is o)
s = Set[int]
for c in cs[:126]:
    Set[c]
Set[int]
for c in cs[:5]:
    List[c]
print(Set[int] is s)

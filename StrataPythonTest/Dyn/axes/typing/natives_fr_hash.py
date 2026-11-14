from typing import List
a = List['int'].__args__[0]
print(hash(a) == hash(List['int'].__args__[0]))

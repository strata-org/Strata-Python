from typing import List, Optional, ForwardRef
a = List['int'].__args__[0]
b = Optional['X'].__args__[0]
print(repr(a), repr(b), type(a).__name__, isinstance(a, ForwardRef))
print(a == List['int'].__args__[0], a == b, a == 'int')
print(repr(a | int), repr(int | a))
print(a.__forward_arg__, a.__forward_evaluated__)

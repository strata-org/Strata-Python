# In-place operators: boundary case. A Union type makes it impossible to know
# statically whether += mutates or rebinds.
"""In-place operators: boundary case.
A Union type makes it impossible to know statically whether += mutates or rebinds.
"""
from typing import Union

def ambiguous_iadd(x: Union[int, list], y) -> Union[int, list]:
    old_id = id(x)
    x += y
    # For int: x is a NEW object (old_id != id(x))
    # For list: x is the SAME object (old_id == id(x))
    print(f"Same object: {id(x) == old_id}")
    return x

if __name__ == "__main__":
    ambiguous_iadd(5, 1)         # Same object: False (int rebinds)
    ambiguous_iadd([1, 2], [3])  # Same object: True  (list mutates)

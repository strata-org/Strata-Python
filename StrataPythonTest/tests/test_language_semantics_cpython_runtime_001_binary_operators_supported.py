# Binary operators: supported case. Types are statically known, so slot
# dispatch collapses to inlined semantics.
"""Binary operators: supported case.
Types are statically known, so slot dispatch collapses to inlined semantics.
"""

def add_ints(x: int, y: int) -> int:
    return x + y

def mul_floats(x: float, y: float) -> float:
    return x * y

def concat_strs(a: str, b: str) -> str:
    return a + b

def mixed_add(x: int, y: float) -> float:
    return x + y

if __name__ == "__main__":
    print(add_ints(3, 4))        # 7
    print(mul_floats(2.5, 3.0))  # 7.5
    print(concat_strs("hello", " world"))  # hello world
    print(mixed_add(1, 2.5))     # 3.5

# In-place operators: supported case. Types are known, so we can determine
# mutation vs rebinding statically.
"""In-place operators: supported case.
Types are known, so we can determine mutation vs rebinding statically.
"""

def increment_int(x: int) -> int:
    x += 1  # rebind: x = x + 1 (new object)
    return x

def extend_list(lst: list[int], extra: list[int]) -> list[int]:
    lst += extra  # mutate: lst.extend(extra), returns same object
    return lst

if __name__ == "__main__":
    print(increment_int(5))  # 6

    original = [1, 2, 3]
    result = extend_list(original, [4, 5])
    print(result)                    # [1, 2, 3, 4, 5]
    print(original is result)        # True (mutated in place)

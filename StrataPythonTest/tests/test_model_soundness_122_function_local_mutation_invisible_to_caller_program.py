# Function-local mutation invisible to caller — consolidated: dict/list/class
# params are copies; mutations lost
"""
A function that modifies a local variable (including parameters) cannot
affect the caller's copy. This is the FUNDAMENTAL consequence of "no
mutation in place" for function calls. Every function operates on
independent copies of its arguments.

This finding consolidates the pattern across all types: int, str, list,
dict, and class instances all behave the same way — modifications inside
a function are invisible to the caller.
"""
from dataclasses import dataclass


@dataclass
class Config:
    value: int


def try_modify_int(x: int) -> None:
    x = x + 100  # rebinds local x; caller's variable unchanged


def try_modify_str(s: str) -> None:
    s = s + " modified"  # rebinds local s


def try_modify_list(lst: list[int]) -> None:
    lst = lst + [99]  # rebinds local lst (NOT iadd)
    # Note: even lst.append(99) would be invisible under value semantics


def try_modify_dict(d: dict[str, int]) -> None:
    d["new"] = 42  # modifies local copy


def try_modify_object(c: Config) -> None:
    c.value = 999  # modifies local copy


def main() -> None:
    # Int: immutable in both models (no divergence)
    n: int = 5
    try_modify_int(n)
    assert n == 5  # both models agree

    # Str: immutable in both models (no divergence)
    s: str = "hello"
    try_modify_str(s)
    assert s == "hello"  # both models agree

    # List: CPython mutates through reference, model doesn't
    lst: list[int] = [1, 2, 3]
    try_modify_list(lst)
    # CPython with `lst = lst + [99]`: lst unchanged (rebind, not iadd)
    # CPython with `lst.append(99)`: lst changed (mutation)
    # Model: lst unchanged regardless
    assert lst == [1, 2, 3]  # both agree for rebind case

    # Dict: CPython mutates through reference
    d: dict[str, int] = {"a": 1}
    try_modify_dict(d)
    # CPython: d["new"] == 42 (mutated through reference)
    # Model: d unchanged (local copy modified)
    assert "new" in d  # CPython: True, Model: False
    assert d["new"] == 42

    # Object: CPython mutates through reference
    c: Config = Config(value=0)
    try_modify_object(c)
    # CPython: c.value == 999 (mutated through reference)
    # Model: c.value == 0 (local copy modified)
    assert c.value == 999

    print(n, s, d.get("new", -1), c.value)


main()

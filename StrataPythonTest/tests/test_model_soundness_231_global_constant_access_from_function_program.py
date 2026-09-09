# Module-level constant access — functions referencing globals need scope
# resolution or inlining; without it, names are unbound (Hole)
"""
Module-level constants accessed from functions. Finding 126 noted this.
The model must make global constants available inside function bodies.

    MAX_RETRIES = 3
    def retry() -> int:
        return MAX_RETRIES  # must resolve to 3

If the translator doesn't inline or scope-resolve module-level names,
the function body can't access them — result is Hole or NameError.

Uses ONLY confirmed-accepted constructs: module-level variable, function.
"""

MAX_SIZE: int = 100
DEFAULT_NAME: str = "unknown"
PI_APPROX: float = 3.14159


def get_max_size() -> int:
    return MAX_SIZE


def is_within_bounds(x: int) -> bool:
    return 0 <= x and x < MAX_SIZE


def circle_area(radius: float) -> float:
    return PI_APPROX * radius * radius


def greet(name: str) -> str:
    if len(name) == 0:
        return "hello " + DEFAULT_NAME
    return "hello " + name


def use_multiple_globals() -> int:
    """Access multiple module-level constants in one function."""
    size: int = MAX_SIZE
    name: str = DEFAULT_NAME
    return size + len(name)  # 100 + 7 = 107


def main() -> None:
    assert get_max_size() == 100
    assert is_within_bounds(50) == True
    assert is_within_bounds(100) == False
    assert is_within_bounds(-1) == False
    assert circle_area(1.0) == 3.14159
    assert greet("alice") == "hello alice"
    assert greet("") == "hello unknown"
    assert use_multiple_globals() == 107

    print(get_max_size(), is_within_bounds(50), greet(""))


main()

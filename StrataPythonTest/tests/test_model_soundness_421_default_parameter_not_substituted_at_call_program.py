# Default parameter not substituted — `greet("World")` with `prefix="Hello"`
# default; translator must insert default at call site
"""
DEFAULT PARAMETER NOT SUBSTITUTED AT CALL SITE

CPython: def greet(name: str, prefix: str = "Hello") -> str:
             return prefix + " " + name
         greet("World") → "Hello World" (default substituted)

Model:   If translator doesn't substitute default at call site:
         greet("World") → greet("World", ???)
         prefix parameter is unbound or Hole → result is Hole

         The translator must recognize that greet("World") has
         fewer arguments than parameters and substitute the default
         value "Hello" for the missing `prefix` argument.

CPython result: "Hello World"
Model result: Hole (prefix not substituted)
"""


def greet(name: str, prefix: str = "Hello") -> str:
    return prefix + " " + name


def clamp(value: int, low: int = 0, high: int = 100) -> int:
    if value < low:
        return low
    if value > high:
        return high
    return value


def repeat(s: str, n: int = 1) -> str:
    return s * n


def increment(x: int, step: int = 1) -> int:
    return x + step


def main() -> None:
    # Test 1: one default
    assert greet("World") == "Hello World"
    assert greet("World", "Hi") == "Hi World"

    # Test 2: two defaults
    assert clamp(50) == 50
    assert clamp(-5) == 0
    assert clamp(200) == 100
    assert clamp(50, 10, 90) == 50
    assert clamp(5, 10, 90) == 10

    # Test 3: default with different type
    assert repeat("ab") == "ab"
    assert repeat("ab", 3) == "ababab"

    # Test 4: simple default
    assert increment(5) == 6
    assert increment(5, 10) == 15

    print("all passed")


main()

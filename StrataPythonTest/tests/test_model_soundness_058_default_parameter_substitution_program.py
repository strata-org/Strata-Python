# Default parameter values may not be substituted at call sites — calls with
# fewer args than params produce wrong arity or Hole
"""
When a function has a parameter with a default value, and the function
is called without that argument, the default is used. In CPython, default
values are evaluated ONCE at function definition time and stored on the
function object. For immutable defaults (int, str, None), this is fine.

The Laurel model must correctly substitute the default value when the
argument is omitted. If the translator doesn't handle default arguments
(treating all parameters as required), calls with fewer arguments than
parameters will fail or produce wrong results.
"""


def greet(name: str, greeting: str = "Hello") -> str:
    return greeting + " " + name


def increment(n: int, step: int = 1) -> int:
    return n + step


def clamp(value: int, low: int = 0, high: int = 100) -> int:
    if value < low:
        return low
    if value > high:
        return high
    return value


def main() -> None:
    # Using default
    assert greet("Alice") == "Hello Alice"
    # Overriding default
    assert greet("Bob", "Hi") == "Hi Bob"

    # Using default step
    assert increment(5) == 6
    # Overriding step
    assert increment(5, 3) == 8

    # Multiple defaults: use all defaults
    assert clamp(50) == 50
    assert clamp(-5) == 0
    assert clamp(200) == 100
    # Override one default
    assert clamp(50, 10) == 50
    assert clamp(5, 10) == 10
    # Override both defaults
    assert clamp(50, 0, 40) == 40

    print(greet("Alice"), increment(5), clamp(50))


main()

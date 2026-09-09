# Module-level variable access — functions reading global constants need scope
# resolution or inlining
"""
Module-level variables (constants, configuration) can be read by
functions. The model must make these values available inside function
bodies. If the translator only handles local variables and parameters,
module-level reads return Hole.
"""

MAX_RETRIES: int = 3
DEFAULT_TIMEOUT: int = 30
PI_APPROX: float = 3.14159


def get_max_retries() -> int:
    return MAX_RETRIES


def circle_area(radius: float) -> float:
    return PI_APPROX * radius * radius


def with_timeout(value: int) -> int:
    if value <= 0:
        return DEFAULT_TIMEOUT
    return value


def retry_loop(attempts: int) -> int:
    """Use module-level constant as loop bound."""
    count: int = 0
    i: int = 0
    while i < MAX_RETRIES and i < attempts:
        count = count + 1
        i = i + 1
    return count


def main() -> None:
    # Read module-level constants
    assert get_max_retries() == 3
    assert with_timeout(0) == 30
    assert with_timeout(60) == 60

    # Use in computation
    area: float = circle_area(1.0)
    assert area > 3.0 and area < 3.2

    # Use as loop bound
    assert retry_loop(10) == 3  # capped at MAX_RETRIES
    assert retry_loop(2) == 2   # capped at attempts

    print(get_max_retries(), with_timeout(0), retry_loop(10))


main()

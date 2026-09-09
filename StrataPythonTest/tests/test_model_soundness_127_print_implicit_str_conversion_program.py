# `print()` implicit str() conversion — should be modeled as pure no-op; must
# not fail on non-string args
"""
`print()` accepts any number of arguments of any type. It calls str()
on each argument before outputting. The subset models print as a "pure
logging effect" — but the implicit str() conversion on non-string args
requires the same str() model as f-strings (finding 083/053).

If print's arguments aren't converted to strings, the model may try to
"print" a from_int value directly, which has no meaning in the model.
"""


def print_int(x: int) -> None:
    print(x)  # implicitly calls str(x)


def print_multiple(name: str, age: int, score: float) -> None:
    print(name, age, score)  # str() on each non-str arg


def print_bool(flag: bool) -> None:
    print(flag)  # prints "True" or "False"


def print_result(label: str, value: int) -> None:
    print(label, value)


def main() -> None:
    # print with various types
    print_int(42)           # "42"
    print_multiple("Alice", 30, 95.5)  # "Alice 30 95.5"
    print_bool(True)        # "True"
    print_result("score:", 100)  # "score: 100"

    # print is modeled as pure (no return value, no side effects on model state)
    # The key question: does the model need to actually convert args to strings?
    # Or can it just treat print as a no-op?

    print("done")


main()

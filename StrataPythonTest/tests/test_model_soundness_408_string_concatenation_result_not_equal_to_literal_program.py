# String concat result ≠ literal — `"a"+"b" == "ab"` unprovable; str_concat
# uninterpreted; must map to SMT-LIB `str.++`
"""
STRING CONCATENATION RESULT NOT EQUAL TO LITERAL — UNPROVABLE

CPython: "hello" + " " + "world" == "hello world" → True (always)

Model:   str_concat(str_concat("hello", " "), "world")
         == "hello world"
         → UNPROVABLE if str_concat is uninterpreted

         The solver doesn't know that concatenating "hello", " ", "world"
         produces "hello world". Without mapping to SMT-LIB str.++,
         string concatenation results are opaque.

Finding 252 identified this. This finding provides the MINIMAL program
that fails: a simple string equality check after concatenation.
"""


def greet(name: str) -> str:
    """Build greeting by concatenation."""
    return "Hello, " + name + "!"


def build_path(directory: str, filename: str) -> str:
    """Build file path."""
    return directory + "/" + filename


def check_greeting() -> bool:
    """Verify concatenation produces expected result."""
    result: str = greet("World")
    # CPython: "Hello, World!" == "Hello, World!" → True
    # Model: str_concat(str_concat("Hello, ", "World"), "!") == "Hello, World!"
    #         → UNPROVABLE (str_concat is uninterpreted)
    return result == "Hello, World!"


def check_path() -> bool:
    """Verify path construction."""
    path: str = build_path("/home", "file.txt")
    return path == "/home/file.txt"


def concat_length() -> bool:
    """len(a + b) == len(a) + len(b) — needs axiom."""
    a: str = "hello"
    b: str = " world"
    result: str = a + b
    # CPython: len("hello world") == 11 == 5 + 6
    # Model: len(str_concat(a, b)) == ??? (no axiom connecting len and concat)
    return len(result) == len(a) + len(b)


def empty_concat_identity() -> bool:
    """s + "" == s — identity axiom."""
    s: str = "test"
    return s + "" == s


def main() -> None:
    assert check_greeting()
    assert check_path()
    assert concat_length()
    assert empty_concat_identity()

    # Additional: associativity
    a: str = "a"
    b: str = "b"
    c: str = "c"
    assert (a + b) + c == a + (b + c)  # associativity

    print("all passed")


main()

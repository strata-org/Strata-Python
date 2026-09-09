# Subset allows 9 string methods but none have models —
# startswith/endswith/find/replace map to SMT-LIB; others need axioms
"""
The subset explicitly says these string methods are IN:
  str.split(), str.join(), str.strip(), str.lower(), str.upper(),
  str.startswith(), str.endswith(), str.find(), str.replace()

But findings 019, 133, 134, 135, 138, 144 identified that NONE of
these have Laurel models. Results are Hole (unconstrained).

This finding provides a SINGLE program using ALL allowlisted string
methods, demonstrating the scope of the gap.

Uses ONLY confirmed-accepted constructs: str methods from allowlist.
"""


def parse_csv_line(line: str) -> list[str]:
    """Uses split — no model."""
    return line.split(",")


def join_words(words: list[str]) -> str:
    """Uses join — no model."""
    return " ".join(words)


def clean_input(s: str) -> str:
    """Uses strip + lower — no model for either."""
    return s.strip().lower()


def shout(s: str) -> str:
    """Uses upper — no model."""
    return s.upper()


def check_prefix(s: str, prefix: str) -> bool:
    """Uses startswith — no model."""
    return s.startswith(prefix)


def check_suffix(s: str, suffix: str) -> bool:
    """Uses endswith — no model."""
    return s.endswith(suffix)


def find_char(s: str, target: str) -> int:
    """Uses find — no model."""
    return s.find(target)


def sanitize(s: str) -> str:
    """Uses replace — no model."""
    return s.replace("<", "").replace(">", "")


def process_input(raw: str) -> str:
    """Combines multiple string methods — ALL produce Hole."""
    cleaned: str = raw.strip()
    lowered: str = cleaned.lower()
    result: str = lowered.replace(" ", "_")
    return result


def main() -> None:
    # split
    assert parse_csv_line("a,b,c") == ["a", "b", "c"]

    # join
    assert join_words(["hello", "world"]) == "hello world"

    # strip + lower
    assert clean_input("  Hello  ") == "hello"

    # upper
    assert shout("hello") == "HELLO"

    # startswith / endswith
    assert check_prefix("hello", "hel") == True
    assert check_prefix("hello", "xyz") == False
    assert check_suffix("hello.py", ".py") == True

    # find
    assert find_char("hello", "l") == 2
    assert find_char("hello", "z") == -1

    # replace
    assert sanitize("<script>") == "script"

    # combined
    assert process_input("  Hello World  ") == "hello_world"

    print(clean_input("  Hi  "), find_char("abc", "b"),
          process_input("  Test  "))


main()

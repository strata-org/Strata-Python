# @dataclass Optional field default None — requires findings 157+223+081+062
# all working: defaults, disjunctive tags, field presence, narrowing
"""
A @dataclass field with `Optional[int] = None` default means:
- The field CAN be None (tag set: {from_int, from_None})
- If not provided at construction, it IS None
- If provided, it's the given value

The model must distinguish between:
1. Field explicitly set to None: `User(name="x", age=None)`
2. Field defaulting to None: `User(name="x")` (age omitted)

Both produce the same result (age is None), but the translator must
handle case 2 by substituting the default (finding 157).

Uses ONLY Frontend-subset features: @dataclass, Optional, int, str, None.
"""
from dataclasses import dataclass
from typing import Optional


@dataclass
class User:
    name: str
    email: Optional[str] = None
    age: Optional[int] = None


def create_minimal() -> User:
    """Only required field provided; optionals default to None."""
    return User(name="alice")


def create_with_email() -> User:
    """One optional provided, other defaults."""
    return User(name="bob", email="bob@example.com")


def create_full() -> User:
    """All fields provided."""
    return User(name="carol", email="carol@x.com", age=30)


def create_explicit_none() -> User:
    """Explicitly pass None — same as default."""
    return User(name="dave", email=None, age=None)


def check_optional_field(u: User) -> str:
    """Access optional field with None check."""
    if u.email is not None:
        return u.email
    return "no email"


def has_age(u: User) -> bool:
    return u.age is not None


def main() -> None:
    minimal: User = create_minimal()
    assert minimal.name == "alice"
    assert minimal.email is None
    assert minimal.age is None

    with_email: User = create_with_email()
    assert with_email.email == "bob@example.com"
    assert with_email.age is None

    full: User = create_full()
    assert full.age == 30

    explicit: User = create_explicit_none()
    assert explicit.email is None

    assert check_optional_field(minimal) == "no email"
    assert check_optional_field(with_email) == "bob@example.com"

    assert has_age(minimal) == False
    assert has_age(full) == True

    print(check_optional_field(minimal), has_age(full),
          minimal.name)


main()

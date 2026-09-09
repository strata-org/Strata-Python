# Dataclass with Optional field — `age: Optional[int] = None` needs tag set
# `{from_None, from_int}` + narrowing
"""
A @dataclass with an Optional field: `field: Optional[int] = None`.
The field can hold either an int or None. Construction with and without
the field, plus access with is-None guards.
"""
from dataclasses import dataclass
from typing import Optional


@dataclass
class UserProfile:
    name: str
    age: Optional[int]
    email: Optional[str]


def create_minimal(name: str) -> UserProfile:
    return UserProfile(name=name, age=None, email=None)


def create_full(name: str, age: int, email: str) -> UserProfile:
    return UserProfile(name=name, age=age, email=email)


def get_age_or_default(p: UserProfile, default: int) -> int:
    if p.age is not None:
        return p.age
    return default


def has_email(p: UserProfile) -> bool:
    return p.email is not None


def main() -> None:
    # Minimal: Optional fields are None
    p1: UserProfile = create_minimal("Alice")
    assert p1.name == "Alice"
    assert p1.age is None
    assert p1.email is None

    # Full: Optional fields have values
    p2: UserProfile = create_full("Bob", 30, "bob@example.com")
    assert p2.name == "Bob"
    assert p2.age == 30
    assert p2.email == "bob@example.com"

    # Access with guard
    assert get_age_or_default(p1, 0) == 0
    assert get_age_or_default(p2, 0) == 30

    # Check Optional field
    assert has_email(p1) == False
    assert has_email(p2) == True

    print(p1.name, get_age_or_default(p1, 0), has_email(p2))


main()

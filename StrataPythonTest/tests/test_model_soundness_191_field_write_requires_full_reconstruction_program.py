# Field write requires full ClassInstance reconstruction — `obj.x = v` must
# rebuild entire value with updated attrs and rebind variable
"""
`from_ClassInstance(name, attrs)` is a VALUE. Writing `obj.x = v` doesn't
mutate — it must construct an ENTIRELY NEW ClassInstance with the updated
attrs dict. The old ClassInstance is unchanged.

This means every field write is a FULL RECONSTRUCTION:
  obj.x = 5
  →  obj = from_ClassInstance(classname(obj), DictStrAny_set(attrs(obj), "x", 5))

If the class has 10 fields and you write 1, you still rebuild all 10.
More critically: the translator must emit this reconstruction. If it
just calls DictStrAny_set on the attrs without rebinding obj, the
write is lost.

This finding tests multi-field classes where writing one field must
preserve all others.

Uses ONLY confirmed-accepted constructs: @dataclass, field write, int, str.
"""
from dataclasses import dataclass


@dataclass
class Person:
    name: str
    age: int
    score: int


def write_one_field_preserves_others() -> bool:
    p: Person = Person(name="alice", age=30, score=100)
    p.age = 31  # write age, name and score must be preserved
    return p.name == "alice" and p.age == 31 and p.score == 100


def write_multiple_fields_sequentially() -> Person:
    p: Person = Person(name="bob", age=25, score=0)
    p.age = 26
    p.score = 50
    p.name = "BOB"
    # All three writes must be visible
    return p


def write_then_read_different_field() -> int:
    p: Person = Person(name="carol", age=40, score=200)
    p.score = 999
    # Reading age must still work (not corrupted by score write)
    return p.age  # 40


def write_in_conditional(p: Person, flag: bool) -> Person:
    if flag:
        p.score = p.score + 10
    # After conditional: score is either original or +10
    return p


def main() -> None:
    # Write one, preserve others
    assert write_one_field_preserves_others() == True

    # Sequential writes
    result: Person = write_multiple_fields_sequentially()
    assert result.name == "BOB"
    assert result.age == 26
    assert result.score == 50

    # Write doesn't corrupt other fields
    assert write_then_read_different_field() == 40

    # Conditional write
    p1: Person = Person(name="x", age=1, score=100)
    p2: Person = write_in_conditional(p1, True)
    assert p2.score == 110
    p3: Person = write_in_conditional(Person(name="x", age=1, score=100), False)
    assert p3.score == 100

    print(result.name, result.age, result.score)


main()

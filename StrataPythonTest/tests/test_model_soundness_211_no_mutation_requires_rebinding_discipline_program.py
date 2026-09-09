# No mutation in place — complete rebinding catalog: every field write,
# append, dict set, augmented assign requires variable rebinding
"""
"No mutation in place" means EVERY modification requires rebinding.
This creates a DISCIPLINE the programmer must follow:

  WRONG:  obj.x = 5          (mutation lost if obj not rebound)
  RIGHT:  obj = new_obj(...)  (explicit rebind)

  WRONG:  lst.append(x)      (list unchanged without rebind)
  RIGHT:  lst = lst + [x]    (or: lst.append(x) with translator rebinding)

The model is SOUND only if the translator correctly rebinds after every
"mutation." This finding catalogs ALL patterns that require rebinding
and tests that the rebinding discipline produces correct results.

Uses ONLY confirmed-accepted constructs: @dataclass, list, dict, int.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


def field_write_rebind() -> int:
    """Field write requires rebinding the object variable."""
    p: Point = Point(x=1, y=2)
    # Under value semantics, p.x = 10 must rebind p
    p = Point(x=10, y=p.y)  # explicit functional style
    return p.x  # 10


def list_append_rebind() -> int:
    """list.append requires rebinding the list variable."""
    xs: list[int] = [1, 2, 3]
    xs.append(4)  # translator must rebind xs internally
    return len(xs)  # 4


def dict_set_rebind() -> int:
    """dict[k] = v requires rebinding the dict variable."""
    d: dict[str, int] = {"a": 1}
    d["b"] = 2  # translator must rebind d internally
    return len(d)  # 2


def multiple_rebinds_in_sequence() -> Point:
    """Each modification rebinds; order matters."""
    p: Point = Point(x=0, y=0)
    p = Point(x=1, y=p.y)   # x=1, y=0
    p = Point(x=p.x, y=2)   # x=1, y=2
    p = Point(x=p.x + 10, y=p.y + 10)  # x=11, y=12
    return p


def rebind_in_loop() -> list[int]:
    """Each iteration rebinds the accumulator."""
    result: list[int] = []
    i: int = 0
    while i < 5:
        result.append(i)  # rebinds result each iteration
        i = i + 1
    return result


def conditional_rebind(p: Point, flag: bool) -> Point:
    """Rebind only on one branch — both paths must be valid."""
    if flag:
        p = Point(x=p.x + 1, y=p.y)
    return p


def main() -> None:
    assert field_write_rebind() == 10
    assert list_append_rebind() == 4
    assert dict_set_rebind() == 2

    result: Point = multiple_rebinds_in_sequence()
    assert result.x == 11 and result.y == 12

    assert rebind_in_loop() == [0, 1, 2, 3, 4]

    assert conditional_rebind(Point(x=5, y=5), True).x == 6
    assert conditional_rebind(Point(x=5, y=5), False).x == 5

    print(field_write_rebind(), list_append_rebind(), result.x)


main()

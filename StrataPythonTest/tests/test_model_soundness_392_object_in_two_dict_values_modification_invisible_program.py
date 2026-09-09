# Object in two dict values — modification through one key invisible; SOUND
# under reassignment (not mutation); AST must reject `d[k].field = v`
"""
OBJECT IN TWO DICT VALUES — MODIFICATION THROUGH ONE KEY INVISIBLE

CPython: d = {"a": obj, "b": obj}  → both values are SAME object
         d["a"].x = 99 → d["b"].x is also 99 (aliased!)

Model:   d = {"a": copy_of_obj, "b": copy_of_obj}
         Modifying d["a"].x doesn't affect d["b"].x (independent copies)

The subset bans `b = a` for mutable types. But storing the same
object under two dict keys creates an alias that's harder to detect.
"""
from dataclasses import dataclass


@dataclass
class Config:
    value: int


def store_same_object_two_keys() -> bool:
    """Same object stored under two keys — aliased in CPython."""
    cfg: Config = Config(10)
    d: dict[str, Config] = {}
    d["primary"] = cfg
    d["backup"] = cfg
    # CPython: d["primary"] and d["backup"] are SAME object
    # Model: two independent copies of Config(10)

    # "Modify" primary (functional style: create new)
    d["primary"] = Config(99)

    # In CPython with mutation: d["backup"].value would be 99
    # In CPython with reassignment: d["backup"].value is still 10
    # In model: d["backup"].value is 10 (independent copy)
    return d["backup"].value == 10


def store_in_list_and_dict() -> bool:
    """Same object in list AND dict — cross-container alias."""
    cfg: Config = Config(5)
    lst: list[Config] = [cfg]
    d: dict[str, Config] = {"key": cfg}

    # Functional update of list element
    lst[0] = Config(99)

    # Dict value should be unchanged (functional style)
    return d["key"].value == 5


def multiple_list_positions() -> bool:
    """Same object at multiple list positions."""
    cfg: Config = Config(7)
    xs: list[Config] = [cfg, cfg, cfg]

    # Modify first position
    xs[0] = Config(100)

    # Other positions unchanged (functional style)
    return xs[1].value == 7 and xs[2].value == 7


def main() -> None:
    # Under functional style (no in-place mutation), all are correct
    # Value semantics matches CPython when using reassignment (not mutation)
    assert store_same_object_two_keys()
    assert store_in_list_and_dict()
    assert multiple_list_positions()

    print("all passed")


main()

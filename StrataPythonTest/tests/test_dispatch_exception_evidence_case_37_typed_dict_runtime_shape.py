"""TypedDict is a static shape tag but an ordinary dict at runtime."""

from typing import NotRequired, TypedDict


def witness(
    case_id,
    operation,
    situation,
    expected,
    action,
    selector,
    modeled=True,
):
    try:
        action()
    except BaseException as error:
        observed = type(error)
        assert observed is expected, (
            f"{case_id}: expected {expected.__name__}, "
            f"observed {observed.__name__}"
        )
        return {
            "id": case_id,
            "operation": operation,
            "key": ["Movie"],
            "selector": selector,
            "situation": situation,
            "expected_exception": expected.__name__,
            "observed_exception": observed.__name__,
            "modeled_row": modeled,
        }
    raise AssertionError(f"{case_id}: expected {expected.__name__}, no exception")


class Movie(TypedDict):
    title: str
    rating: NotRequired[int]


def read_optional_absent():
    movie = Movie(title="Alien")
    return movie["rating"]


def read_required_after_forbidden_delete():
    movie = Movie(title="Alien")
    del movie["title"]
    return movie["title"]


def read_dynamic_missing():
    movie = Movie(title="Alien")
    key = "missing"
    return movie[key]


def read_dynamic_unhashable():
    movie = Movie(title="Alien")
    key = []
    return movie[key]


def membership_dynamic_unhashable():
    movie = Movie(title="Alien")
    return [] in movie


EVIDENCE = (
    witness(
        "typed_dict.optional_field_absent",
        "subscript_read",
        "an optional declared key is absent",
        KeyError,
        read_optional_absent,
        "rating",
    ),
    witness(
        "typed_dict.required_field_after_shape_violation",
        "subscript_read",
        "ordinary dict deletion removes a required key; PyHard rejects this write",
        KeyError,
        read_required_after_forbidden_delete,
        "title",
        modeled=False,
    ),
    witness(
        "typed_dict.dynamic_missing_key",
        "subscript_read",
        "a dynamic hashable key is not one of the present fields",
        KeyError,
        read_dynamic_missing,
        None,
    ),
    witness(
        "typed_dict.dynamic_unhashable_key",
        "subscript_read",
        "a dynamic key is a mutable list and therefore has no hash",
        TypeError,
        read_dynamic_unhashable,
        None,
    ),
    witness(
        "typed_dict.membership_unhashable_key",
        "membership",
        "TypedDict key membership receives an unhashable list",
        TypeError,
        membership_dynamic_unhashable,
        None,
    ),
)

runtime_value = Movie(title="Alien")
runtime_value["extra"] = "accepted by CPython"
runtime_value["title"] = 42
CONTROLS = {
    "runtime_type": type(runtime_value).__name__,
    "extra_key_accepted": runtime_value["extra"],
    "wrong_value_type_accepted": runtime_value["title"],
}

RESULT = tuple(item["observed_exception"] for item in EVIDENCE)

"""Exact exception witnesses for iteration, next, and membership."""


def witness(case_id, operation, key, situation, expected, action, modeled=True):
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
            "key": [key],
            "selector": None,
            "situation": situation,
            "expected_exception": expected.__name__,
            "observed_exception": observed.__name__,
            "modeled_row": modeled,
        }
    raise AssertionError(f"{case_id}: expected {expected.__name__}, no exception")


class InvalidIterator:
    def __iter__(self):
        return 1


EVIDENCE = (
    witness(
        "iteration.missing",
        "iterate",
        "int",
        "the runtime type has neither __iter__ nor legacy __getitem__",
        TypeError,
        lambda: iter(1),
    ),
    witness(
        "iteration.invalid_iter_result",
        "iterate",
        "InvalidIterator",
        "__iter__ returns an object with no __next__",
        TypeError,
        lambda: iter(InvalidIterator()),
    ),
    witness(
        "next.missing",
        "next",
        "int",
        "the runtime type has no __next__ special method",
        TypeError,
        lambda: next(1),
    ),
    witness(
        "next.exhausted",
        "next",
        "tuple_iterator",
        "the selected __next__ reports iterator exhaustion",
        StopIteration,
        lambda: next(iter(())),
        modeled=False,
    ),
    witness(
        "membership.dict.unhashable_needle",
        "membership",
        "dict",
        "dict key membership receives an unhashable list",
        TypeError,
        lambda: [] in {},
    ),
    witness(
        "membership.set.unhashable_needle",
        "membership",
        "set",
        "set membership receives an unhashable list",
        TypeError,
        lambda: [] in set(),
    ),
    witness(
        "membership.frozenset.unhashable_needle",
        "membership",
        "frozenset",
        "frozenset membership receives an unhashable list",
        TypeError,
        lambda: [] in frozenset(),
    ),
    witness(
        "membership.str.non_str_needle",
        "membership",
        "str",
        "string containment receives a non-string needle",
        TypeError,
        lambda: 1 in "123",
    ),
    witness(
        "membership.bytes.invalid_needle_type",
        "membership",
        "bytes",
        "bytes containment receives neither bytes nor an integer index",
        TypeError,
        lambda: [] in b"abc",
    ),
    witness(
        "membership.bytes.integer_out_of_range",
        "membership",
        "bytes",
        "bytes containment receives an integer outside 0..255",
        ValueError,
        lambda: 256 in b"abc",
    ),
    witness(
        "membership.unsupported_container",
        "membership",
        "object",
        "the container has no contains, iteration, or sequence protocol",
        TypeError,
        lambda: 1 in object(),
    ),
)

CONTROLS = {
    "iteration": list(iter((1, 2))),
    "next": next(iter((1,))),
    "dict_membership": "key" in {"key": 1},
    "str_membership": "2" in "123",
    "bytes_membership_bytes": b"b" in b"abc",
    "bytes_membership_int": 98 in b"abc",
}

RESULT = tuple(item["observed_exception"] for item in EVIDENCE)

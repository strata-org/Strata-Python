"""Exact exception witnesses for truth conversion and len()."""


def witness(case_id, operation, key, situation, expected, action):
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
        }
    raise AssertionError(f"{case_id}: expected {expected.__name__}, no exception")


class BadBoolReturn:
    def __bool__(self):
        return 1


class BadLengthReturn:
    def __len__(self):
        return "one"


class NegativeLength:
    def __len__(self):
        return -1


class HugeLength:
    def __len__(self):
        return 1 << 100


EVIDENCE = (
    witness(
        "truth.bool.non_bool_result",
        "truth",
        "BadBoolReturn",
        "__bool__ returns int rather than an actual bool",
        TypeError,
        lambda: bool(BadBoolReturn()),
    ),
    witness(
        "truth.len.non_index_result",
        "truth",
        "BadLengthReturn",
        "fallback __len__ returns a value with no integer index",
        TypeError,
        lambda: bool(BadLengthReturn()),
    ),
    witness(
        "truth.len.negative_result",
        "truth",
        "NegativeLength",
        "fallback __len__ returns a negative integer",
        ValueError,
        lambda: bool(NegativeLength()),
    ),
    witness(
        "truth.len.result_overflow",
        "truth",
        "HugeLength",
        "fallback __len__ exceeds Py_ssize_t",
        OverflowError,
        lambda: bool(HugeLength()),
    ),
    witness(
        "length.missing",
        "length",
        "object",
        "the runtime type has no __len__ special method",
        TypeError,
        lambda: len(object()),
    ),
    witness(
        "length.non_index_result",
        "length",
        "BadLengthReturn",
        "__len__ returns a value with no integer index",
        TypeError,
        lambda: len(BadLengthReturn()),
    ),
    witness(
        "length.negative_result",
        "length",
        "NegativeLength",
        "__len__ returns a negative integer",
        ValueError,
        lambda: len(NegativeLength()),
    ),
    witness(
        "length.result_overflow",
        "length",
        "HugeLength",
        "__len__ exceeds Py_ssize_t",
        OverflowError,
        lambda: len(HugeLength()),
    ),
)

CONTROLS = {
    "default_object_truth": bool(object()),
    "empty_list_truth": bool([]),
    "list_length": len([1, 2]),
}

RESULT = tuple(item["observed_exception"] for item in EVIDENCE)

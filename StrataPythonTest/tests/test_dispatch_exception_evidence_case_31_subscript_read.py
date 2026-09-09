"""Exact exception witnesses for builtin subscript reads."""


def witness(case_id, key, situation, expected, action):
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
            "operation": "subscript_read",
            "key": [key],
            "selector": None,
            "situation": situation,
            "expected_exception": expected.__name__,
            "observed_exception": observed.__name__,
        }
    raise AssertionError(f"{case_id}: expected {expected.__name__}, no exception")


def unsupported_receiver():
    value = 1
    return value[0]


def list_invalid_key_type():
    value = [1]
    key = "0"
    return value[key]


def tuple_invalid_key_type():
    value = (1,)
    key = "0"
    return value[key]


def str_invalid_key_type():
    value = "a"
    key = "0"
    return value[key]


def bytes_invalid_key_type():
    value = b"a"
    key = "0"
    return value[key]


EVIDENCE = (
    witness(
        "subscript.read.list.out_of_range",
        "list",
        "an integer index remains outside the list after negative normalization",
        IndexError,
        lambda: [1][4],
    ),
    witness(
        "subscript.read.tuple.out_of_range",
        "tuple",
        "an integer index remains outside the tuple after negative normalization",
        IndexError,
        lambda: (1,)[4],
    ),
    witness(
        "subscript.read.str.out_of_range",
        "str",
        "an integer index remains outside the string after negative normalization",
        IndexError,
        lambda: "a"[4],
    ),
    witness(
        "subscript.read.bytes.out_of_range",
        "bytes",
        "an integer index remains outside the bytes value after normalization",
        IndexError,
        lambda: b"a"[4],
    ),
    witness(
        "subscript.read.list.invalid_key_type",
        "list",
        "the key is neither index-convertible nor a slice",
        TypeError,
        list_invalid_key_type,
    ),
    witness(
        "subscript.read.tuple.invalid_key_type",
        "tuple",
        "the key is neither index-convertible nor a slice",
        TypeError,
        tuple_invalid_key_type,
    ),
    witness(
        "subscript.read.str.invalid_key_type",
        "str",
        "the key is neither index-convertible nor a slice",
        TypeError,
        str_invalid_key_type,
    ),
    witness(
        "subscript.read.bytes.invalid_key_type",
        "bytes",
        "the key is neither index-convertible nor a slice",
        TypeError,
        bytes_invalid_key_type,
    ),
    witness(
        "subscript.read.list.zero_slice_step",
        "list",
        "the slice step is zero",
        ValueError,
        lambda: [1][::0],
    ),
    witness(
        "subscript.read.tuple.zero_slice_step",
        "tuple",
        "the slice step is zero",
        ValueError,
        lambda: (1,)[::0],
    ),
    witness(
        "subscript.read.str.zero_slice_step",
        "str",
        "the slice step is zero",
        ValueError,
        lambda: "a"[::0],
    ),
    witness(
        "subscript.read.bytes.zero_slice_step",
        "bytes",
        "the slice step is zero",
        ValueError,
        lambda: b"a"[::0],
    ),
    witness(
        "subscript.read.dict.missing_key",
        "dict",
        "a hashable key has no equality-class entry in the dict",
        KeyError,
        lambda: {}["missing"],
    ),
    witness(
        "subscript.read.dict.unhashable_key",
        "dict",
        "the key is a mutable list and therefore has no hash",
        TypeError,
        lambda: {}[[]],
    ),
    witness(
        "subscript.read.unsupported_receiver",
        "int",
        "the receiver type has no item-read protocol",
        TypeError,
        unsupported_receiver,
    ),
)

CONTROLS = {
    "list_index": [1][0],
    "tuple_slice": (1, 2)[0:1],
    "str_slice": "ab"[0:1],
    "bytes_slice": b"ab"[0:1],
    "dict_hit": {"present": 1}["present"],
}

RESULT = tuple(item["observed_exception"] for item in EVIDENCE)

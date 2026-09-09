"""Exact exception witnesses for builtin subscript writes."""


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
            "operation": "subscript_write",
            "key": [key],
            "selector": None,
            "situation": situation,
            "expected_exception": expected.__name__,
            "observed_exception": observed.__name__,
        }
    raise AssertionError(f"{case_id}: expected {expected.__name__}, no exception")


def list_out_of_range():
    values = [1]
    values[4] = 2


def list_invalid_key_type():
    values = [1]
    values["0"] = 2


def list_zero_slice_step():
    values = [1]
    values[::0] = []


def list_extended_slice_length_mismatch():
    values = [1, 2, 3, 4]
    values[::2] = [9]


def dict_unhashable_key():
    values = {}
    values[[]] = 1


def tuple_write():
    values = (1,)
    values[0] = 2


def str_write():
    value = "a"
    value[0] = "b"


def bytes_write():
    value = b"a"
    value[0] = 98


EVIDENCE = (
    witness(
        "subscript.write.list.out_of_range",
        "list",
        "an integer target index is outside the list",
        IndexError,
        list_out_of_range,
    ),
    witness(
        "subscript.write.list.invalid_key_type",
        "list",
        "the target key is neither index-convertible nor a slice",
        TypeError,
        list_invalid_key_type,
    ),
    witness(
        "subscript.write.list.zero_slice_step",
        "list",
        "the target slice step is zero",
        ValueError,
        list_zero_slice_step,
    ),
    witness(
        "subscript.write.list.extended_slice_length_mismatch",
        "list",
        "extended-slice replacement length differs from the selected length",
        ValueError,
        list_extended_slice_length_mismatch,
    ),
    witness(
        "subscript.write.dict.unhashable_key",
        "dict",
        "the target key is a mutable list and therefore has no hash",
        TypeError,
        dict_unhashable_key,
    ),
    witness(
        "subscript.write.tuple.immutable",
        "tuple",
        "tuple has no item-assignment protocol",
        TypeError,
        tuple_write,
    ),
    witness(
        "subscript.write.str.immutable",
        "str",
        "str has no item-assignment protocol",
        TypeError,
        str_write,
    ),
    witness(
        "subscript.write.bytes.immutable",
        "bytes",
        "bytes has no item-assignment protocol",
        TypeError,
        bytes_write,
    ),
)

normal_list = [1]
normal_list[0] = 2
normal_dict = {}
normal_dict["key"] = 3
CONTROLS = {
    "list_store": normal_list,
    "dict_store": normal_dict,
}

RESULT = tuple(item["observed_exception"] for item in EVIDENCE)

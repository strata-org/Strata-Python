"""Exact exception witnesses for certified builtin binary leaves."""


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
            "key": list(key),
            "selector": None,
            "situation": situation,
            "expected_exception": expected.__name__,
            "observed_exception": observed.__name__,
        }
    raise AssertionError(f"{case_id}: expected {expected.__name__}, no exception")


HUGE_FLOAT_CONVERSION = 10**10000
HUGE_COUNT = 10**100


EVIDENCE = (
    witness(
        "numeric.true_divide.zero",
        "binary_true_divide",
        ("int", "int"),
        "the right operand is zero",
        ZeroDivisionError,
        lambda: 1 / 0,
    ),
    witness(
        "numeric.floor_divide.zero",
        "binary_floor_divide",
        ("float", "float"),
        "the right operand is floating-point zero",
        ZeroDivisionError,
        lambda: 1.0 // 0.0,
    ),
    witness(
        "numeric.modulo.zero",
        "binary_modulo",
        ("int", "int"),
        "the right operand is zero",
        ZeroDivisionError,
        lambda: 1 % 0,
    ),
    witness(
        "numeric.add.int_to_float_overflow",
        "binary_add",
        ("int", "float"),
        "the integer operand cannot be converted to finite float",
        OverflowError,
        lambda: HUGE_FLOAT_CONVERSION + 1.0,
    ),
    witness(
        "numeric.left_shift.negative_count",
        "binary_lshift",
        ("int", "int"),
        "the shift count is negative",
        ValueError,
        lambda: 1 << -1,
    ),
    witness(
        "numeric.left_shift.count_overflow",
        "binary_lshift",
        ("int", "int"),
        "the shift count cannot be represented by the runtime",
        OverflowError,
        lambda: 1 << HUGE_COUNT,
    ),
    witness(
        "numeric.power.zero_negative_exponent",
        "binary_power",
        ("int", "int"),
        "zero is raised to a negative integral exponent",
        ZeroDivisionError,
        lambda: 0**-1,
    ),
    witness(
        "numeric.bitwise.unsupported_float",
        "binary_and",
        ("int", "float"),
        "bitwise and receives a float operand",
        TypeError,
        lambda: 1 & 1.0,
    ),
    witness(
        "repeat.str.count_overflow",
        "binary_multiply",
        ("str", "int"),
        "the string repeat count cannot be represented",
        OverflowError,
        lambda: "x" * HUGE_COUNT,
    ),
    witness(
        "repeat.bytes.count_overflow",
        "binary_multiply",
        ("bytes", "int"),
        "the bytes repeat count cannot be represented",
        OverflowError,
        lambda: b"x" * HUGE_COUNT,
    ),
    witness(
        "repeat.list.count_overflow",
        "binary_multiply",
        ("list", "int"),
        "the list repeat count cannot be represented",
        OverflowError,
        lambda: [1] * HUGE_COUNT,
    ),
    witness(
        "repeat.tuple.count_overflow",
        "binary_multiply",
        ("tuple", "int"),
        "the tuple repeat count cannot be represented",
        OverflowError,
        lambda: (1,) * HUGE_COUNT,
    ),
)

CONTROLS = {
    "true_divide": 3 / 2,
    "left_shift": 3 << 1,
    "power": 2**3,
    "str_repeat": "x" * 2,
    "bytes_repeat": b"x" * 2,
    "list_repeat": [1] * 2,
    "tuple_repeat": (1,) * 2,
}

RESULT = tuple(item["observed_exception"] for item in EVIDENCE)

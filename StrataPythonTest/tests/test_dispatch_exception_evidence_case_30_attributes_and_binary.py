"""Exact exception witnesses for attribute and binary dispatch."""


def witness(case_id, operation, key, situation, expected, action, selector=None):
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
            "selector": selector,
            "situation": situation,
            "expected_exception": expected.__name__,
            "observed_exception": observed.__name__,
        }
    raise AssertionError(f"{case_id}: expected {expected.__name__}, no exception")


class Plain:
    pass


class ReadOnly:
    @property
    def value(self):
        return 1


def read_missing_attribute():
    return Plain().missing


def write_read_only_property():
    value = ReadOnly()
    value.value = 2


def unsupported_binary_pair():
    return 1 + "x"


EVIDENCE = (
    witness(
        "attribute.read.missing",
        "attr_read",
        ("Plain",),
        "ordinary lookup exhausts the stable MRO without finding 'missing'",
        AttributeError,
        read_missing_attribute,
        selector="missing",
    ),
    witness(
        "attribute.write.property_without_setter",
        "attr_write",
        ("ReadOnly",),
        "the selected property is a data descriptor with no setter",
        AttributeError,
        write_read_only_property,
        selector="value",
    ),
    witness(
        "binary.add.unsupported_exact_pair",
        "binary_add",
        ("int", "str"),
        "int.__add__ and str.__radd__ do not produce a value",
        TypeError,
        unsupported_binary_pair,
    ),
)

CONTROLS = {
    "property_read": ReadOnly().value,
    "integer_addition": 1 + 2,
}

RESULT = tuple(item["observed_exception"] for item in EVIDENCE)

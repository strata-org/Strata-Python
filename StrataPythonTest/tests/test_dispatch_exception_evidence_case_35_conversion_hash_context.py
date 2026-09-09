"""Exact exception witnesses for conversion, hashing, and context lookup."""


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


class BadString:
    def __str__(self):
        return 1


class BadRepresentation:
    def __repr__(self):
        return 1


class MissingEnter:
    def __exit__(self, exception_type, exception, traceback):
        return False


class MissingExit:
    def __enter__(self):
        return self


class GoodContext:
    def __enter__(self):
        return 7

    def __exit__(self, exception_type, exception, traceback):
        return False


def use_missing_enter():
    with MissingEnter():
        pass


def use_missing_exit():
    with MissingExit():
        pass


def use_good_context():
    with GoodContext() as value:
        return value


EVIDENCE = (
    witness(
        "string.non_str_result",
        "string",
        "BadString",
        "__str__ returns int rather than str",
        TypeError,
        lambda: str(BadString()),
    ),
    witness(
        "representation.non_str_result",
        "representation",
        "BadRepresentation",
        "__repr__ returns int rather than str",
        TypeError,
        lambda: repr(BadRepresentation()),
    ),
    witness(
        "hash.disabled",
        "hash",
        "list",
        "list has __hash__ disabled",
        TypeError,
        lambda: hash([]),
    ),
    witness(
        "hash.nested_unhashable",
        "hash",
        "tuple",
        "tuple hashing reaches an unhashable list element",
        TypeError,
        lambda: hash(([],)),
    ),
    witness(
        "context.enter.missing",
        "context_enter",
        "MissingEnter",
        "the manager type has no __enter__ special method",
        TypeError,
        use_missing_enter,
    ),
    witness(
        "context.exit.missing",
        "context_exit",
        "MissingExit",
        "the manager type has no __exit__ special method",
        TypeError,
        use_missing_exit,
    ),
)

CONTROLS = {
    "builtin_string": str(1),
    "builtin_representation": repr(1),
    "hashable_tuple": hash((1, 2)),
    "context_manager": use_good_context(),
}

RESULT = tuple(item["observed_exception"] for item in EVIDENCE)

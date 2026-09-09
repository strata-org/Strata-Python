# Case 11 matching and boundaries
class RootError(Exception):
    pass


class LeafError(RootError):
    pass


class OtherError(Exception):
    pass


class ConstructionError(Exception):
    def __init__(self):
        raise OtherError("constructor failed")


def broad_handler_first():
    try:
        raise LeafError("leaf")
    except RootError:
        return "root"
    except LeafError:
        return "leaf"


def specific_handler_first():
    try:
        raise LeafError("leaf")
    except LeafError:
        return "leaf"
    except RootError:
        return "root"


def tuple_handler():
    try:
        raise LeafError("leaf")
    except (OtherError, RootError):
        return "tuple"


def exception_does_not_catch_base_exception():
    try:
        try:
            raise SystemExit("stop")
        except Exception:
            return "Exception"
    except BaseException as caught:
        return type(caught).__name__


def handler_exception_skips_siblings():
    try:
        try:
            raise RootError("first")
        except RootError:
            raise OtherError("second")
        except OtherError:
            return "sibling"
    except OtherError:
        return "outer"


def exception_during_raise_normalization():
    try:
        raise ConstructionError
    except OtherError:
        return "OtherError"
    except ConstructionError:
        return "ConstructionError"


RESULT = (
    broad_handler_first(),
    specific_handler_first(),
    tuple_handler(),
    exception_does_not_catch_base_exception(),
    handler_exception_skips_siblings(),
    exception_during_raise_normalization(),
)

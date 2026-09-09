class ArgumentError(Exception):
    pass


class BodyError(Exception):
    pass


class Empty:
    pass


def failed_default_leaves_function_name_unbound():
    try:
        def created(value=1 // 0):
            return value
    except ZeroDivisionError:
        pass

    try:
        return created()
    except UnboundLocalError:
        return "UnboundLocalError"


def argument():
    raise ArgumentError("argument")


def body(value):
    raise BodyError("body")


def argument_error_precedes_body():
    try:
        body(argument())
    except ArgumentError:
        return "ArgumentError"
    except BodyError:
        return "BodyError"


def lookup_error_precedes_argument():
    try:
        Empty().missing(argument())
    except AttributeError:
        return "AttributeError"
    except ArgumentError:
        return "ArgumentError"


def body_requires_one(value):
    raise BodyError("body")


def binding_error_precedes_body():
    try:
        body_requires_one()
    except TypeError:
        return "TypeError"
    except BodyError:
        return "BodyError"


RESULT = (
    failed_default_leaves_function_name_unbound(),
    argument_error_precedes_body(),
    lookup_error_precedes_argument(),
    binding_error_precedes_body(),
)

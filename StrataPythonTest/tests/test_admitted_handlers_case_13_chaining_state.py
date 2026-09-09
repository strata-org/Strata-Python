class OuterError(Exception):
    pass


class InnerError(Exception):
    pass


def raise_inner():
    raise InnerError("inner")


def implicit_context():
    try:
        try:
            raise OuterError("outer")
        except OuterError:
            raise InnerError("inner")
    except InnerError as error:
        return (
            type(error.__context__).__name__,
            error.__cause__ is None,
            error.__suppress_context__,
        )


def context_crosses_call_boundary():
    try:
        try:
            raise OuterError("outer")
        except OuterError:
            raise_inner()
    except InnerError as error:
        return type(error.__context__).__name__


def explicit_cause():
    cause = OuterError("cause")
    try:
        raise InnerError("inner") from cause
    except InnerError as error:
        return (
            type(error.__cause__).__name__,
            error.__context__ is None,
            error.__suppress_context__,
        )


def suppressed_context_is_retained():
    try:
        try:
            raise OuterError("outer")
        except OuterError:
            raise InnerError("inner") from None
    except InnerError as error:
        return (
            error.__cause__ is None,
            type(error.__context__).__name__,
            error.__suppress_context__,
        )


def bare_reraise_adds_no_context():
    try:
        try:
            raise OuterError("outer")
        except OuterError:
            raise
    except OuterError as error:
        return error.__context__ is None


RESULT = (
    implicit_context(),
    context_crosses_call_boundary(),
    explicit_cause(),
    suppressed_context_is_retained(),
    bare_reraise_adds_no_context(),
)

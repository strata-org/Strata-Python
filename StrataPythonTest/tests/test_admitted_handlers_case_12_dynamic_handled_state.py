class OuterError(Exception):
    pass


class InnerError(Exception):
    pass


def reraiser():
    raise


def reraised_from_callee():
    try:
        try:
            raise OuterError("outer")
        except OuterError:
            reraiser()
    except OuterError as caught:
        return str(caught)


def restored_after_nested_handler():
    try:
        raise OuterError("outer")
    except OuterError:
        try:
            raise InnerError("inner")
        except InnerError:
            pass

        try:
            reraiser()
        except OuterError as caught:
            return str(caught)


def reraised_from_unwinding_finally():
    try:
        try:
            raise OuterError("outer")
        finally:
            reraiser()
    except OuterError as caught:
        return str(caught)


def no_active_exception():
    try:
        reraiser()
    except RuntimeError:
        return "RuntimeError"


RESULT = (
    reraised_from_callee(),
    restored_after_nested_handler(),
    reraised_from_unwinding_finally(),
    no_active_exception(),
)

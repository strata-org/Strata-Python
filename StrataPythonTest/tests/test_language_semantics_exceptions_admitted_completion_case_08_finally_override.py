# Case 08 finally override
class PendingError(Exception):
    pass


class ReplacementError(Exception):
    pass


def return_over_return():
    try:
        return "pending return"
    finally:
        return "finally return"


def return_over_exception():
    try:
        raise PendingError("pending")
    finally:
        return "finally return"


def raise_over_return():
    try:
        return "pending return"
    finally:
        raise ReplacementError("replacement")


def observe_raise_over_return():
    try:
        raise_over_return()
    except ReplacementError:
        return "ReplacementError"


def raise_over_exception():
    try:
        try:
            raise PendingError("pending")
        finally:
            raise ReplacementError("replacement")
    except ReplacementError as error:
        return str(error), type(error.__context__).__name__


def break_over_exception():
    for _ in [0]:
        try:
            raise PendingError("pending")
        finally:
            break
    return "after break"


def continue_over_exception():
    iterations = 0
    for _ in [0, 1]:
        try:
            iterations += 1
            raise PendingError("pending")
        finally:
            continue
    return iterations


RESULT = (
    return_over_return(),
    return_over_exception(),
    observe_raise_over_return(),
    raise_over_exception(),
    break_over_exception(),
    continue_over_exception(),
)

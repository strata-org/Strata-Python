# Case 24 exception string failure
class FormattingError(Exception):
    pass


class BadStringError(Exception):
    def __str__(self):
        raise FormattingError("format failed")


def string_failure_inside_handler():
    try:
        try:
            raise BadStringError("original")
        except BadStringError as error:
            str(error)
    except FormattingError as replacement:
        context_type = type(replacement.__context__).__name__
        try:
            error
        except UnboundLocalError:
            target_state = "UnboundLocalError"
        else:
            target_state = "bound"
        return str(replacement), context_type, target_state


RESULT = string_failure_inside_handler()

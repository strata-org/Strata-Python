# Case 21 except star merge
def unmatched_remainder():
    handled = "not handled"
    try:
        try:
            raise ExceptionGroup(
                "source",
                [ValueError("v"), KeyError("k")],
            )
        except* ValueError:
            handled = "handled"
    except ExceptionGroup as remainder:
        remainder_types = tuple(
            [type(item).__name__ for item in remainder.exceptions]
        )
    return handled, remainder_types


def raised_handler_is_merged_with_remainder():
    try:
        try:
            raise ExceptionGroup(
                "source",
                [ValueError("v"), KeyError("k")],
            )
        except* ValueError:
            raise TypeError("handler")
    except BaseExceptionGroup as merged:
        first_type = type(merged.exceptions[0]).__name__
        second = merged.exceptions[1]
        second_type = type(second).__name__
        remainder_types = tuple(
            [type(item).__name__ for item in second.exceptions]
        )
        return (
            merged.message,
            first_type,
            second_type,
            remainder_types,
        )


RESULT = unmatched_remainder(), raised_handler_is_merged_with_remainder()

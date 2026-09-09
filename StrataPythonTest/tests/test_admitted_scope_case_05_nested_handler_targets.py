class OuterError(Exception):
    pass


class InnerError(Exception):
    pass


def reused_target():
    try:
        raise OuterError("outer")
    except OuterError as error:
        outer_before = str(error)
        try:
            raise InnerError("inner")
        except InnerError as error:
            inner_value = str(error)

        try:
            error
        except UnboundLocalError:
            target_after_inner = "UnboundLocalError"
        else:
            target_after_inner = "still bound"

        try:
            raise
        except OuterError as reraised:
            active_after_inner = str(reraised)

        return (
            outer_before,
            inner_value,
            target_after_inner,
            active_after_inner,
        )


def distinct_targets():
    try:
        raise OuterError("outer")
    except OuterError as outer:
        outer_before = str(outer)
        try:
            raise InnerError("inner")
        except InnerError as inner:
            inner_value = str(inner)
        outer_after = str(outer)
        return outer_before, inner_value, outer_after


RESULT = reused_target(), distinct_targets()

class LocalLookupError(KeyError):
    pass


def ordered_handlers(flag: bool) -> int:
    try:
        if flag:
            raise LocalLookupError()
        raise ValueError()
    except LookupError as lookup_error:
        return 1
    except ValueError as value_error:
        return 2


def unmatched_reaches_outer() -> int:
    try:
        try:
            raise LocalLookupError()
        except ValueError as wrong_error:
            return 0
    except LookupError as outer_error:
        return 3


def bare_reraise() -> int:
    try:
        try:
            raise LocalLookupError()
        except LookupError as active_error:
            raise
    except LocalLookupError as reraised_error:
        return 4

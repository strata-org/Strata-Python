class CapturedError(Exception):
    pass


class ReplacementError(Exception):
    pass


def return_target() -> CapturedError:
    try:
        raise CapturedError("returned")
    except CapturedError as caught:
        return caught


def save_then_fallthrough() -> CapturedError:
    try:
        raise CapturedError("saved")
    except CapturedError as caught:
        saved = caught
    return saved


def save_then_replacement() -> CapturedError:
    try:
        try:
            raise CapturedError("survives replacement")
        except CapturedError as caught:
            saved = caught
            raise ReplacementError("replacement")
    except ReplacementError as replacement:
        pass
    return saved

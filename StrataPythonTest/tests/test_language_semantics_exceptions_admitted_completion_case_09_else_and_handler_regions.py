# Case 09 else and handler regions
class E(Exception):
    pass


def normal_uses_else():
    try:
        pass
    except E:
        return "handler"
    else:
        return "else"


def exception_uses_handler():
    try:
        raise E("caught")
    except E:
        return "handler"
    else:
        return "else"


def return_skips_else():
    try:
        return "try return"
    except E:
        return "handler"
    else:
        return "else"


def break_skips_else():
    for _ in [0]:
        try:
            break
        except E:
            return "handler"
        else:
            return "try else"
    return "after break"


def continue_skips_else():
    result = "after continue"
    for _ in [0]:
        try:
            continue
        except E:
            return "handler"
        else:
            result = "try else"
    return result


def exception_in_else_escapes_same_handlers():
    marker = 0
    try:
        try:
            pass
        except KeyError:
            return "same handler", marker
        else:
            raise KeyError("from else")
        finally:
            marker = 1
    except KeyError:
        return "outer handler", marker


RESULT = (
    normal_uses_else(),
    exception_uses_handler(),
    return_skips_else(),
    break_skips_else(),
    continue_skips_else(),
    exception_in_else_escapes_same_handlers(),
)

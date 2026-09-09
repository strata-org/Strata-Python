class E(Exception):
    pass


module_name = "module value"


def handler_never_matches():
    try:
        before = module_name
    except UnboundLocalError:
        before = "UnboundLocalError"

    try:
        pass
    except E as module_name:
        pass

    try:
        after = module_name
    except UnboundLocalError:
        after = "UnboundLocalError"
    return before, after


def builtin_is_also_shadowed():
    try:
        before = len([1])
    except UnboundLocalError:
        before = "UnboundLocalError"

    try:
        pass
    except E as len:
        pass

    try:
        after = len([1])
    except UnboundLocalError:
        after = "UnboundLocalError"
    return before, after


RESULT = handler_never_matches(), builtin_is_also_shadowed()

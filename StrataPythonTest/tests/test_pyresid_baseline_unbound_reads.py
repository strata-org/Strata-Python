def maybe_local(flag: bool) -> int:
    if flag:
        local_value = 1
    return local_value


def unknown_global() -> int:
    return missing_global


def catch_local() -> str:
    try:
        value = maybe_local(False)
        return "missed-local-error"
    except UnboundLocalError:
        return "caught-local-error"


def catch_global() -> str:
    try:
        value = unknown_global()
        return "missed-global-error"
    except NameError:
        return "caught-global-error"


local_result = catch_local()
global_result = catch_global()

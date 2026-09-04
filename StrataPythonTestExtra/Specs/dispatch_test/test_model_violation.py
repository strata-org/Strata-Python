from servicelib.Contract import modeled_text


def check_violating_call() -> bool:
    value = modeled_text("")
    return value is not None

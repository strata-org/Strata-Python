import servicelib.Contract


def check_dotted_violation() -> bool:
    value = servicelib.Contract.modeled_text("")
    return value is not None

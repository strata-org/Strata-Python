import servicelib.Contract


def check_dotted_call() -> bool:
    value = servicelib.Contract.modeled_text("key")
    return value is not None

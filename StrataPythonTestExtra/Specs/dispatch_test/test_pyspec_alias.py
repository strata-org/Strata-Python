from servicelib.Contract import modeled_text as mt


def check_alias_call() -> bool:
    value = mt("key")
    return value is not None

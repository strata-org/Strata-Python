import servicelib.Contract as sc


def check_module_alias_call() -> bool:
    value = sc.modeled_text("key")
    return value is not None

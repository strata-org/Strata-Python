import servicelib


def require_dynamic_values_nonempty_bad() -> bool:
    client = servicelib.connect("storage")
    client.require_dynamic_values_nonempty(Items={"alice": ""})
    return True

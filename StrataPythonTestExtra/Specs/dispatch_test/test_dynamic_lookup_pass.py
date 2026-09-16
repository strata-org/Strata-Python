import servicelib


def require_dynamic_values_nonempty_ok() -> bool:
    client = servicelib.connect("storage")
    client.require_dynamic_values_nonempty(
        Items={"alice": "x", "bob": "y"})
    return True

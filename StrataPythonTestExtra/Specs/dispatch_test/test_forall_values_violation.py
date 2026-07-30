import servicelib

def require_values_nonempty_bad() -> bool:
    client = servicelib.connect("storage")
    # The empty value "" violates `len(v) >= 1`.
    client.require_values_nonempty(Items={"alice": ""})
    return True

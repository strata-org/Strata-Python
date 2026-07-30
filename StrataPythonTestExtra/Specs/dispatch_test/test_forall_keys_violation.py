import servicelib

def require_keys_nonempty_bad() -> bool:
    client = servicelib.connect("storage")
    # The empty key "" violates `len(k) >= 1`.
    client.require_keys_nonempty(Items={"": "x"})
    return True

import servicelib

def require_all_nonempty_empty() -> bool:
    client = servicelib.connect("storage")
    # An empty list satisfies `for k in Keys: ...` vacuously.
    client.require_all_nonempty(Keys=[])
    return True

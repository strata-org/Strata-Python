# Intentional: finally return overrides try return (use with caution)
def get_default():
    try:
        return compute_value()
    except:
        pass
    finally:
        return -1  # fallback
def compute_value(): raise RuntimeError
assert get_default() == -1
print("OK: return in finally — provides fallback value")

# A type-selective handler (`except ValueError:`) is rejected in --v2 until
# native exception dispatch lands: the current encoding enters the handler for
# ANY in-flight exception, so a selective handler would silently catch
# exceptions it must not. Catch-alls (`except:` / `except Exception:`) stay
# supported.

def typed() -> int:
    result: int = 0
    try:
        result = 1
    except ValueError:
        result = 2
    return result

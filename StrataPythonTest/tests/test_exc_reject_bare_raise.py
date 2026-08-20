# Bare `raise` (re-raise) is deliberately rejected in --v2: it re-raises the
# exception "currently being handled" via an implicit dynamic lookup. It was
# previously mistranslated as a Hole (re-raising an arbitrary value).

def reraise() -> int:
    result: int = 0
    try:
        raise Exception("inner")
    except Exception:
        result = 1
        raise
    return result

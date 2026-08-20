# `raise ... from ...` (exception chaining) is deliberately rejected in --v2:
# chaining mutates the exception's __cause__ at runtime, a dynamic exception
# feature outside the supported subset.

def chain() -> int:
    try:
        raise Exception("inner")
    except Exception:
        raise Exception("outer") from Exception("cause")
    return 0

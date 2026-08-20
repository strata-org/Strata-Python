# `except*` (exception groups, PEP 654) is deliberately rejected in --v2:
# subgroup matching with residual re-raise has no counterpart in the supported
# exception subset.

def group() -> int:
    result: int = 0
    try:
        result = 1
    except* Exception:
        result = 2
    return result

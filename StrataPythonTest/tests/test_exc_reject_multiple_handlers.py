# Multiple `except` handlers are rejected in --v2 until native exception
# dispatch lands: the current encoding has no type dispatch, so it would run
# the handlers as one concatenated blob (a KeyError running a ValueError
# handler) — a silent mistranslation.

def multi() -> int:
    result: int = 0
    try:
        result = 1
    except ValueError:
        result = 2
    except KeyError:
        result = 3
    return result

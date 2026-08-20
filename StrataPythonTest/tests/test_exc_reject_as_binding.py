# `except ... as e` is rejected in --v2 until native exception support lands:
# the caught value is not reconstructible under the current encoding, so
# binding it would hand the handler a fabricated value.

def bound() -> int:
    result: int = 0
    try:
        result = 1
    except Exception as e:
        result = 2
    return result

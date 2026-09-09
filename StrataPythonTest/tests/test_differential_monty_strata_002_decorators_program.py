# Feature: USER-DEFINED FUNCTION DECORATORS (worklist item 2).
#
# Monty result (pydantic-monty 0.0.18, the running oracle):
#   identity(-5)  ->  value -5      [RUN]   (decorator is NOT applied; no guard)
# CPython 3.14.3:
#   identity(-5)  ->  raises AssertionError  (decorator IS applied; guard fires)
# Strata front end:
#   translates the function but DROPS `_decorator_list` (PythonToLaurel.lean:2230),
#   so it models `identity` as the undecorated body `lambda x: x` -> verifies SAFE.
#
# Why this program matters (the soundness crux):
#   - Frontend's verdict (SAFE, returns -5, no exception) is UNSOUND vs CPython,
#     which raises AssertionError. This is why decorators sit in cell (B) under
#     the project's CPython-grounded soundness standard.
#   - But Monty 0.0.18 ALSO drops the decorator and returns -5. So Frontend's
#     verdict matches Monty EXACTLY. Under the inheritance premise (oracle =
#     Monty), the same encoding is SOUND -> the cell collapses to (A).
#   Decorators are the clearest case in this corpus where "sound" is
#   oracle-relative: two shared CPython-divergent no-ops (Monty's + Frontend's)
#   cancel out.
#
# Everything here is inside Monty's accepted subset (nested def, closure,
# decorator syntax, assert) and is translatable by the Strata front end.


def require_nonneg(f):
    def wrapper(x: int) -> int:
        assert x >= 0, "precondition"
        return f(x)
    return wrapper


@require_nonneg
def identity(x: int) -> int:
    return x


# Observable: on CPython this raises (guard applied); on Monty and under
# Frontend's drop-decorator encoding it is just -5.
identity(-5)

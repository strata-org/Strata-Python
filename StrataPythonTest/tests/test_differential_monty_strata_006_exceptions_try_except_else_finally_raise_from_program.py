# Feature: exceptions — try/except/else/finally, `raise ... from`, exception-TYPE matching.
#
# What this demonstrates (every value below is what CPython & Monty actually produce;
# the comments mark where the Strata front end's CURRENT encoding diverges):
#
#   classify(5)         -> "positive-no-exc"   (try succeeds -> ELSE runs)
#       Strata: drops `else` (test_soundness_try_else_ignored.py) -> "positive". WRONG.
#   classify(-1)        -> "caught-value-error" (ValueError caught by type match)
#       Strata: handler ignores the exception TYPE -> any error hits any handler.
#   finally_overrides() -> 2                    (finally's return overrides try's)
#       Strata: `raise`/return/finally control flow not modeled (finding 160) -> 1. WRONG.
#   reraise_chain()     -> "wrapped"            (raise RuntimeError from e)
#       Monty: runs, but silently drops the `from e` cause (exceptions.md).
#       Strata: `.Raise` is dropped entirely (PythonToLaurel.lean ~1940 FIXME). WRONG.
#
# Monty (pydantic-monty 0.0.18): RUNS. `limitations/language.md` "What does work" lists
#   "try/except/else/finally, raise ... from ...". `limitations/exceptions.md` confirms a
#   fixed built-in exception hierarchy and that `raise X from Y` parses but drops the cause.
#
# Frontend documented stance (frontend-subset.md, "Exceptions"): IN / VERIFIABLE for built-in
#   exceptions with specific `except` clauses. The ACTUAL front-end encoding contradicts
#   this — see analysis.md. This is the silently-unsound gap -> cell (B).


def classify(x: int) -> str:
    try:
        if x < 0:
            raise ValueError("neg")
        result: str = "positive"
    except ValueError:
        result = "caught-value-error"
    else:
        result = result + "-no-exc"  # ELSE: runs only when the try body succeeds
    finally:
        pass  # FINALLY: always runs
    return result


def finally_overrides() -> int:
    try:
        return 1  # deferred...
    finally:
        return 2  # ...overridden by finally's return -> CPython/Monty give 2


def reraise_chain() -> str:
    try:
        try:
            raise ValueError("root")
        except ValueError as e:
            raise RuntimeError("wrapped") from e  # raise-from (cause dropped by Monty)
    except RuntimeError as e2:
        return str(e2)


def main() -> list:
    out: list = []
    out.append(classify(5))           # "positive-no-exc"
    out.append(classify(-1))          # "caught-value-error"
    out.append(finally_overrides())   # 2
    out.append(reraise_chain())       # "wrapped"
    return out


main()

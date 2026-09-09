# Feature CATALOG: the "free exclusions" (F) — dynamism BOTH Monty and Frontend exclude.
#
# This program is written ENTIRELY within both subsets (the "free simplification"
# thesis): the same small task done without classes / match / del / walrus / *args.
# It runs on Monty and CPython; Frontend would translate it.
#
# The substance of this finding is the rejection catalog in analysis.md. Key empirical
# result (pydantic-monty 0.0.18, the running oracle): of the worklist's listed items,
# only `match` and `del` are genuine (F). `class` is (D) (Frontend supports it, Monty
# does not). `walrus` / `*args` / `**kwargs` actually RUN on Monty 0.0.18 despite
# limitations/language.md listing them as rejected -> they are (C), not (F).


def classify(code: int) -> str:
    # if/elif instead of `match` (which both subsets exclude)
    if code == 0:
        return "ok"
    elif code == 1:
        return "warn"
    else:
        return "error"


def total(a: int, b: int, c: int) -> int:
    # fixed positional params instead of *args (which Frontend excludes)
    return a + b + c


def main() -> list:
    return [classify(0), classify(2), total(1, 2, 3)]


main()

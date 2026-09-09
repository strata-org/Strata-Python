# Feature: comprehensions (list/set/dict + generator-expression) and scope isolation.
#
# Monty (pydantic-monty 0.0.18): comprehensions are IN. `limitations/comprehensions.md`
#   says Monty inlines list/set/dict comprehensions per PEP 709 (no synthetic frame;
#   comprehension targets do NOT leak into the enclosing scope). Generator expressions
#   parse but MATERIALIZE TO A LIST (a documented divergence from CPython's lazy iterator).
#
# Strata front end: TRANSLATES every comprehension to `.Hole` —
#   PythonToLaurel.lean:879/883/886/889 (.ListComp/.SetComp/.DictComp/.GeneratorExp
#   => mkStmtExprMd .Hole). A `.Hole` is an UNCONSTRAINED SMT variable; per
#   findings/laurel-encoding-soundness/385, "Hole satisfies any assertion — the solver
#   picks whichever makes the proof work", which yields FALSE verification. So the
#   comprehension's element types, the body's possible exceptions, and any inner
#   assertions are all dropped -> silently unsound.
#
# Frontend documented stance (frontend-subset.md): "List/dict/set comprehensions" OUT and
#   "Generator expressions" OUT (firmly "may grow"). So they are *supposed* to be
#   rejected at the Layer-2 gate, but the front end translates them to Hole instead.
#
# This program runs IDENTICALLY on Monty and CPython (no genexpr indexing, so the
# gen-expr-degradation divergence is not observable here).


def demo() -> list:
    sq: list = [x * x for x in range(4)]              # list comp -> [0, 1, 4, 9]
    evens: set = {x for x in range(6) if x % 2 == 0}  # set comp  -> {0, 2, 4}
    sqmap: dict = {x: x * x for x in range(3)}         # dict comp -> {0:0, 1:1, 2:4}
    total: int = sum(g for g in sq)                    # gen-expr (Monty: materialized) -> 14
    return [sq, sorted(evens), sqmap, total]


def scope_isolation() -> int:
    x: int = 100
    ys: list = [x for x in range(3)]   # PEP 709: the target `x` does NOT leak
    return x                           # CPython & Monty: still 100 (not 2)


def main() -> list:
    return [demo(), scope_isolation()]


main()

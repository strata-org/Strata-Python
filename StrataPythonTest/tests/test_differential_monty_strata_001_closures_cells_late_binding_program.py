# Feature: closures / nested functions with CELL capture and LATE BINDING (+ `nonlocal`).
#
# What this demonstrates:
#   1. make_adder  — a nested function captures a free variable `n` by cell.
#   2. make_counter— a `nonlocal` cell persists and mutates across calls.
#   3. late_binding— the classic late-binding trap: every closure created in the
#                    loop shares ONE cell for `i`, so they all read the FINAL value
#                    of `i` at call time, giving [2, 2, 2] and NOT [0, 1, 2].
#
# Monty result (pydantic-monty 0.0.18): RUNS. Nested functions, closures, and
#   `nonlocal` are all listed under "What does work" in
#   repos/monty/limitations/language.md. Returns [8, 1, 2, 2, 2, 2].
#
# Strata front end: does NOT translate it. A nested `FunctionDef` statement (and a
#   `Nonlocal` statement) is not a handled case in translateStmt; it falls through
#   to the catch-all `throw (.unsupportedConstruct "Statement type not yet
#   supported" ...)` at PythonToLaurel.lean:2119. The front end's own pending
#   scoreboard records test_closure.py / test_nonlocal.py / test_nested_function.py.
#
# Frontend verdict: OUT — rejected at the Layer-2 AST gate. "Closures and nested
#   functions" and `nonlocal` are both explicitly OUT in frontend-subset.md
#   ("Laurel has no closure model today; ... require cell-object modeling";
#   `nonlocal` = "cross-scope mutable state. Incompatible with functional-style
#   translation."). Because the gate REJECTS rather than mis-translates, Frontend is
#   SAFE here (no false "verified"), which makes this cell (C), not (B).


def make_adder(n: int):
    def adder(x: int) -> int:
        return x + n  # free variable `n` read from an enclosing cell
    return adder


def make_counter():
    count: int = 0

    def inc() -> int:
        nonlocal count  # mutable cell shared across every call to inc()
        count = count + 1
        return count

    return inc


def late_binding() -> list[int]:
    fns = []
    for i in range(3):
        def f() -> int:
            return i  # late-bound: reads `i` from the shared cell at CALL time
        fns.append(f)
    return [g() for g in fns]  # CPython & Monty: [2, 2, 2], not [0, 1, 2]


def main() -> list[int]:
    add5 = make_adder(5)
    assert add5(3) == 8, "cell capture"

    c = make_counter()
    first = c()
    second = c()
    assert first == 1 and second == 2, "nonlocal cell persists across calls"

    lb = late_binding()
    assert lb == [2, 2, 2], "late binding shares one cell"

    return [add5(3), first, second, lb[0], lb[1], lb[2]]


main()

# Feature: `global` / `nonlocal` scope declarations (module- and function-scope mutable state).
#
# The Python subtlety at the heart of this: an assignment to a bare name inside a
# function creates a LOCAL unless a `global`/`nonlocal` declaration redirects it to
# an outer scope. So the declaration changes the *binding category* of the name,
# which changes both whether the program runs and what module state it observes.
#
#   bump(2); bump(5)        -> module `counter` becomes 7   (global write)
#   make_local_shadow()     -> returns 999, but module `counter` STAYS 7
#                              (assignment without `global` is a LOCAL, shadows the global)
#   outer()                 -> 7                              (nonlocal write; see finding 001)
#   => main() == [7, 999, 7]
#
# Monty (pydantic-monty 0.0.18): RUNS. `limitations/language.md` "What does work"
#   lists `global` and `nonlocal`. Output matches CPython.
#
# Strata front end: REJECTS. `Global`/`Nonlocal` are not handled statement cases in
#   translateStmt; they hit the catch-all `unsupportedConstruct` at
#   PythonToLaurel.lean:2119. (Even a bare module-global READ is pending —
#   test_global_var.py.) Pending: test_global_keyword.py, test_global_var.py.
#   NOTE: there is NO `test_soundness_global_*` test (contrast the exception cases in
#   finding 006) — the front end rejects rather than silently mis-models. Safe.
#
# Frontend verdict: OUT. frontend-subset.md lists "`global` and `nonlocal` declarations"
#   OUT ("cross-scope mutable state. Incompatible with functional-style translation.")
#   and names them in the Layer-2 AST gate. Rejected => SAFE (no false verify) => cell (C).

counter: int = 0


def bump(n: int) -> None:
    global counter          # redirect the assignment to the MODULE binding
    counter = counter + n


def make_local_shadow() -> int:
    counter = 999           # NO `global`: this is a fresh LOCAL, module global untouched
    return counter


def outer() -> int:
    total: int = 0

    def add(k: int) -> None:
        nonlocal total      # function-scope cell (cross-ref finding 001)
        total = total + k

    add(3)
    add(4)
    return total


def main() -> list:
    bump(2)
    bump(5)
    assert counter == 7, "global write accumulates on the module binding"

    shadowed: int = make_local_shadow()
    assert shadowed == 999, "local assignment returns 999"
    assert counter == 7, "module global is NOT touched by the local shadow"

    nl: int = outer()
    assert nl == 7, "nonlocal write"

    return [counter, shadowed, nl]


main()

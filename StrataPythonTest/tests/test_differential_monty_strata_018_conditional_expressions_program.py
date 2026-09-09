# Feature: CONDITIONAL EXPRESSIONS  x if c else y  (+ boolean and/or short-circuit).
#
# Monty result (pydantic-monty 0.0.18): CPython-faithful LAZY evaluation.
#   def safe_div(x): return 0 if x == 0 else 100 // x
#   [safe_div(0), safe_div(4)]            -> [0, 25]     (MATCH; untaken `100//x` NOT evaluated when x==0)
#   False and t(); True or t() (t has side effect) -> t NEVER called, len(calls)==0 (MATCH; short-circuit)
# CPython 3.14.3 agrees.
#
# Frontend handling: IfExp is translated (PythonToLaurel.lean:772-776) to
# StmtExpr.IfThenElse(cond, thenExpr, elseExpr) — BOTH branches translated EAGERLY.
# Accepted (non-pending) tests with TOTAL branches: test_ifexpr.py,
# test_ternary_true/false/nested.py, test_conditional_assign.py.
#
# The interesting axis is COMPLETENESS, not soundness:
#   * Eager evaluation of both branches is SOUND (the IfThenElse selects the taken
#     branch's value; the untaken value is discarded -> never a wrong "verified").
#   * But a precondition-bearing UNTAKEN branch (division, indexing) emits a proof
#     obligation that the guard was meant to make unreachable, causing a FALSE
#     POSITIVE (spurious "possible division by zero"). That is incompleteness.
#   The pending boolean short-circuit tests are exactly this, and are PLAIN pending
#   (not test_soundness_*): test_bool_shortcircuit_and.py / _or.py
#   ( (x != 0) and (10 // x > 0) with x==0 ).
#
# Matrix cell: (A) — Monty IN, Frontend VERIFIABLE (sound) for total branches. The
# eager-eval incompleteness for guard-protected partial branches is a precision
# caveat shared with boolean and/or, fixed by guarding each branch's side
# conditions under the condition.
#
# This program is in both subsets. It runs on Monty/CPython; the Strata front end
# translates it (and verifies it when branches are total; safe_div's else-branch
# carries a division precondition -> the eager-eval caveat applies).

def safe_div(x: int) -> int:
    # Python evaluates `100 // x` ONLY when x != 0 (lazy ternary).
    return 0 if x == 0 else 100 // x

[safe_div(0), safe_div(4)]

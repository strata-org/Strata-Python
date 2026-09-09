# Feature: STRING OPERATIONS — methods, slicing, concatenation, len, substring `in`.
#
# This program is in BOTH subsets and exercises the feature on the oracle, then
# answers the three step-4 questions.
#
# (1) DOES IT RUN ON MONTY?  Yes — CPython-faithful (pydantic-monty 0.0.18 vs
#     CPython 3.14.3, scripts/monty_diff.py): the value body below returns
#     ['hello', 'HI!', True, 3] on BOTH — MATCH. Methods are native (types/str.rs).
#
# (2) DOES THE STRATA FRONT END TRANSLATE IT?  Yes — it does NOT reject. For a
#     `str`-typed receiver, `x.split()`/`x.upper()` resolve to `str@split`/
#     `str@upper` (refineFunctionCallExpr, PythonToLaurel.lean:991-1037); these
#     have no model (hasModel=false) and `str` is NOT in exhaustiveClasses
#     (populated only from user composites, :2891), so the "Unknown method" reject
#     (:1166-1199) is SKIPPED and the call lowers to `.Hole`.
#
# (3) WOULD FRONTEND'S VERDICT BE SOUND?  NO. `.Hole` is a free, solver-chosen SMT
#     variable: "Hole satisfies any assertion — the solver picks whichever value
#     makes the proof work" (finding 385). So a postcondition/return-type assertion
#     over a string-method result is dischargeable even when FALSE at runtime ->
#     false verification (silent unsoundness, cell B). Witness below.

# --- Soundness witness (the (3) demonstration) ---
# Runtime (Monty/CPython): starts_with_x("banana") -> False  ("banana".startswith
#   doesn't begin with "x"). So `assert ... ` is FALSE -> raises AssertionError.
# Frontend: `s.startswith("x")` -> `.Hole` (bool-typed but unconstrained); the VCG
#   instantiates the Hole to satisfy the assertion -> "verified", though the real
#   value is False. Frontend's verdict (valid) contradicts the runtime -> UNSOUND.
def starts_with_x(s: str) -> bool:
    return s.startswith("x")          # startswith -> .Hole

# --- Plain runnable body (exercises the surface; MATCH on Monty/CPython) ---
def first_word(s: str) -> str:
    return s.split(" ")[0]            # split -> .Hole; [0] -> .Hole

def shout(s: str) -> str:
    return s.upper() + "!"            # upper -> .Hole; concat length unlinked

[first_word("hello world"), shout("hi"), starts_with_x("banana"), len("abc")]

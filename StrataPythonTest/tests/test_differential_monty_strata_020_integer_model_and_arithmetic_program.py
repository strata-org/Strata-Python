# Feature: INTEGER MODEL & ARITHMETIC OPERATORS  // % / **  + unbounded/bignum.
#
# The foundational numeric finding that 014 (augmented assignment) references but
# never roots. Composite, decided per-operator. Monty is CPython-faithful on every
# axis (arbitrary-precision BigInt, floor //, sign-follows-divisor %, float-returning /).
#
# Monty result (pydantic-monty 0.0.18) — all MATCH CPython 3.13.5:
#   7 // -3                     -> -3            floor, toward -inf       (B): SMT Euclidean = -2
#   7 % -3                      -> -2            sign follows DIVISOR     (B): SMT Euclidean = 1
#   -7 % 3                      ->  2            sign follows DIVISOR     (A): b>0 coincides
#   7 / 2                       -> 3.5  (float)  true division -> float   (B): front end havocs to .Hole
#   2 ** 100                    -> 1267650600228229401496703205376        (C): literal/value > 2^30
#   (2**62) * (2**62)           -> 21267647932558653966460912964485513216 (C): i64 fast path -> BigInt
#   (7 // -3) * -3 + (7 % -3)   ->  7            divmod identity holds
#
# Frontend handling (source):
#   //  -> PFloorDiv  -> Laurel/SMT int `/`  (PythonRuntimeLaurelPart.lean:754;
#                        PythonToLaurel.lean:607; lowered .numeric .Div, PythonToCore.lean:174)
#   %   -> PMod       -> Laurel/SMT int `%`  (PythonRuntimeLaurelPart.lean:961; :608)
#   /   -> .Hole      -> SOLVER-CHOSEN value  (PythonToLaurel.lean:606
#                        ".Div _ => return mkStmtExprMd .Hole -- Floating-point are not supported yet")
#   **  -> PPow       -> int_pow / float_pow  (PythonRuntimeLaurelPart.lean:944)
#   int -> unbounded SMT `int` via as_int!/from_int (model is bignum-capable),
#          BUT front end GATES literals to |n| < 2^30 (frontend-subset.md:86; OUT list :411).
#
# SMT-LIB int `/`,`%` are EUCLIDEAN (remainder >= 0). They diverge from Python
# floor-div / sign-mod EXACTLY when the divisor is negative (model.py proves the
# boundary over all integers). For divisor > 0 they coincide -> that slice is sound (A).
#
# This program is the cleanest self-contained (B): a name-target int program whose
# only "dynamism" is a negative divisor. Monty/CPython compute -3; Frontend's PFloorDiv
# (SMT Euclidean) computes -2 and would verify the FALSE assertion `q == -2` as valid.

def floor_div_neg(a: int, b: int) -> int:
    return a // b

# Observable: Monty & CPython -> -3 ; Frontend PFloorDiv (SMT Euclidean) -> -2 (UNSOUND)
floor_div_neg(7, -3)

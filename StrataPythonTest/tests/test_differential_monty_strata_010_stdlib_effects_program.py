# Feature: stdlib effects — re, json, datetime, math, os, sys (classified on the PURITY/EFFECT axis).
#
# Monty ships ALL six (limitations/modules.md): asyncio, datetime, json, math, os, pathlib,
#   re, sys, typing. `math` has wide CPython-3.14-matching coverage; `sys` is minimal
#   (version/platform/stdout markers); `os`/`pathlib` are sandbox-limited.
#
# Frontend documented stance (frontend-subset.md): math IN/allowlisted; re & json "may grow"
#   (OUT); os/sys/pathlib OUT (can't model the OS); datetime not allowlisted (=> OUT).
#
# Strata front end REALITY (the important part):
#   - Unmodeled function calls => `.havocOutputs` (PythonToLaurel.lean:110) => `.Hole`.
#     A `.Hole` is solver-chosen and UNSOUND (findings/laurel-encoding-soundness/385).
#   - `math` is NOT modeled (no math.* in the front end) => math.sqrt/floor => Hole.
#     Float `Div` is also `.Hole` ("Floating-point not supported yet", line 606).
#   - `json` is NOT modeled => json.loads/dumps => Hole. (Its return is HETEROGENEOUS,
#     which Frontend's homogeneous list[T]/dict[K,V] cannot represent anyway.)
#   - `re` HAS a real model: a regex->Core compiler (Regex/ReParser.lean, ReToCore.lean)
#     for a RESTRICTED sublanguage that THROWS `.unimplemented` on lookahead/backrefs/
#     non-greedy quantifiers — i.e. it REJECTS what it can't model (safe).
#   - `datetime` HAS extensive CorePrelude modeling (pure date/time value ops).
#
# This program exercises the PURE subset (math), which runs identically on Monty & CPython.
# Effectful/heterogeneous cases are documented below, not run in main (to stay deterministic).

import math


def pure_math() -> list:
    return [
        math.floor(3.7),     # 3   (pure, deterministic, int-valued)
        math.gcd(12, 8),     # 4
        math.factorial(5),   # 120
        math.isqrt(50),      # 7
    ]


# --- Effectful / heterogeneous stdlib (documented; NOT called from main) ---
# json.loads('[1, "two", 3.0]')  -> [1, 'two', 3.0]   HETEROGENEOUS list (no list[T])
# datetime.now()                 -> nondeterministic (reads the clock)  -> an EFFECT
# os.getcwd() / open(...)        -> environment / filesystem EFFECTS
# sys.platform                   -> "monty" (a constant; pure read)


def main() -> list:
    return pure_math()


main()

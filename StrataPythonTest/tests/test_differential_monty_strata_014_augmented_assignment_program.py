# Feature: AUGMENTED ASSIGNMENT  x += / -= / *= / %= / //= / [i]+=  (out-of-worklist).
#
# Augmented assignment is a COMPOSITE "soundness aggregator": its cell depends
# entirely on the operator and target, inheriting (B) hazards from other findings.
#
# Monty result (pydantic-monty 0.0.18): CPython-faithful on every axis.
#   x = 5; x += 3; x *= 2; x          -> 16            (MATCH)   -> (A) slice
#   x = 10; x %= -3; x                -> -2            (MATCH)   -> (B): Frontend Euclidean = 1
#   x = 10; x //= -3; x               -> -4            (MATCH)   -> (B): Frontend sign bug
#   a=[1]; b=a; a += [2]; b           -> [1, 2]        (MATCH)   -> (B): in-place __iadd__ thru alias
#   f()[g()] += 1 ; calls             -> ['a','i']     (MATCH)   -> eval-ONCE (Frontend fixes index,
#                                                                   reuses base twice: latent (B))
# CPython 3.14.3 agrees with every Monty result above.
#
# Frontend handling (PythonToLaurel.lean:2093-2116, AugAssign): lowers `t op= e` to
# `t = t op e`. For subscript targets it binds the INDEX/slice exprs to
# $augAssignTempVar temps (so the index is evaluated once) but reconstructs the
# target as base[temp] -> the BASE expr appears in both LHS store and RHS load,
# i.e. base is evaluated twice (residual eval-count gap, latent unless base has
# side effects). The op itself inherits mod/floordiv sign unsoundness; list `+=`
# and aliased targets inherit the value-copy aliasing unsoundness (finding 005).
#
# This program is the cleanest self-contained (B): name target, int, no aliasing.
# Monty/CPython give -2 (sign follows divisor); Frontend's Euclidean mod verifies
# it as 1 -> silently unsound (pending test_soundness_augmod_neg.py).

x: int = 10
x %= -3      # Monty/CPython: -2   |   Frontend models Euclidean mod -> 1  (UNSOUND)
x

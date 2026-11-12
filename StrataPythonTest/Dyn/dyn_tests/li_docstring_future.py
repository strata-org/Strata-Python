"""A module with a docstring."""
from __future__ import division
from pyhard import loop_invariant, OLD

def f(n):
    i = 0
    loop_invariant(lambda: i <= n)
    while i < n:
        i += 1
    return i

print(f(1))

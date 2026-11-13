# Test: a quantifier over an old collection whose body reads none of its binders is read wholly at
# entry; one whose body reads its binder reads only the collection at entry; a dict view stays with
# its quantifier.
from pyhard import loop_invariant, OLD

def f(xs, d, n):
    i = 0
    loop_invariant(lambda: all(True for x in OLD(xs)))
    loop_invariant(lambda: all(True for k, v in OLD(d).items()) or True)
    loop_invariant(lambda: all(x > 0 for x in OLD(xs)) or True)
    loop_invariant(lambda: all(v > 0 for k, v in OLD(d).items()) or True)
    while i < n:
        i += 1
    return i

print(f([1, 2], {"a": 1}, 2))

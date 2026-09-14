"""`is` is confined to True, False and None.

Identity is not a function of a value in CPython. Within one code object
constants are deduplicated, so `1000 is 1000` is True, while
`c = 1000; c is int("1000")` is False; small ints and some strings are cached, so
`5 is int("5")` is True. Which equal scalars share an object is an implementation
detail, not language semantics.

So immutable scalars are given no heap location -- sound, because immutability
makes their aliasing unobservable except through `is` and `id`. `id` is a banned
builtin, and `is` is admitted only against the three singletons, where the
language guarantees there is exactly one object.

The accepted forms live in the semantics corpus; these are the rejected ones.
"""

a = 5
b = 5
same_int = a is b

s = "x"
t = "x"
same_str = s is t

xs = [1]
ys = [1]
same_list = xs is not ys

# The four call-shape checks the prologue emits, each reported by raising rather
# than branching so the prologue stays a single straight-line block.
#
# KNOWN DIVERGENCES from CPython, both in wording only:
#  1. Several missing parameters are reported one at a time; CPython aggregates
#     them as "missing 2 required positional arguments: 'x' and 'y'".
#  2. A keyword naming a positional-only parameter is reported as an unexpected
#     keyword; CPython says "got some positional-only arguments passed as keyword
#     arguments". Absorbing it into **kw when one exists already matches.
def h(x):
    print("h", x)
def g(x, y):
    print("g", x, y)
def d(a, b=2):
    print("d", a, b)
def k(a, *, key):
    print("k", a, key)
def po(a, /, b):
    print("po", a, b)
def z():
    print("z")

def t(label, fn, *a, **kw):
    try:
        fn(*a, **kw)
    except TypeError as e:
        print(label + ":", e)

# missing required
t("missing", h)
t("missing_second", g, 1)
# Divergence 1 above: CPython reports both at once here.
t("missing_both", g)
t("missing_kwonly", k, 1)

# too many positional
t("too_many", h, 1, 2)
t("too_many_three", g, 1, 2, 3)
t("too_many_default", d, 1, 2, 3)
# The verb agrees with the runtime count, so it cannot be fixed when the
# message is written: "1 was given" but "2 were given".
t("too_many_one", z, 1)
t("too_many_two", z, 1, 2)

# unexpected keyword
t("unexpected", h, 1, y=3)
t("unexpected_default", d, 1, z=9)

# a parameter given a value twice
t("dup_first", g, 1, x=2)
t("dup_second", g, 1, 2, y=3)

# error precedence: wrong in more than one way at once
t("dup_beats_toomany", g, 1, 2, 3, y=4)

# correct calls still work
h(1)
g(1, 2)
d(1)
k(1, key=2)
po(1, 2)
z()

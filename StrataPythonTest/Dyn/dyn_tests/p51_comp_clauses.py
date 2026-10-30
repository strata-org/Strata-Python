# Comprehension clauses and parts that no other program covers:
# - an `if` between two `for`s, and an `if` after a later `for`;
# - a filter that reads the variable of a later `for` clause: before that clause first runs,
#   the read raises UnboundLocalError; after it runs, the read sees the value the clause left;
# - a walrus in a function's comprehension that a later part of the comprehension reads, once
#   with the function reading the walrus variable after the comprehension and once without;
# - attribute and subscript targets;
# - set and dict elements that are unhashable (a list);
# - an element, a key and a value whose lowering spans several blocks;
# - a comprehension in a filter, and one in a later `for`'s iterable;
# - a comprehension in a `try` body;
# - sum and len of a comprehension;
# - module-level calls of the walrus functions, whose printed results a runner can compare with
#   CPython.
def between(xs, ys):
    return [(x, y) for x in xs if x for y in ys]


def later_if(xs, ys):
    return [(x, y) for x in xs for y in ys if x < y]


def later(xs, ys):
    return [x for x in xs if x == 0 or y for y in ys]


def later_unbound(xs, ys):
    return [x for x in xs if y for y in ys]


def walrus_filter(xs):
    return [y for x in xs if (y := x * 10)], y


def walrus_key(xs):
    return {(k := x * 10): k + 1 for x in xs}, k


def walrus_filter_only(xs):
    return [y for x in xs if (y := x * 10)]


def walrus_key_only(xs):
    return {(k := x * 10): k + 1 for x in xs}


def targets(o, d, xs):
    a = [o.a for o.a in xs]
    b = [d["k"] for d["k"] in xs]
    return a, b


def unhashable(xs):
    s = {[x] for x in xs}
    t = {[x]: x for x in xs}
    return s, t


def blocks(xs, d):
    a = [x if x else -x for x in xs]
    b = {(x and d): (x or d) for x in xs}
    return a, b


def nested(xss):
    a = [xs for xs in xss if [x for x in xs if x]]
    b = [y for xs in xss for y in [x * 2 for x in xs]]
    return a, b


def in_try(xs):
    try:
        return [1 // x for x in xs]
    except ZeroDivisionError:
        return None


def folds(f, xs):
    return sum([f(x) for x in xs]), len({x for x in xs})


def show(label, f):
    try:
        print(label, f())
    except Exception as e:
        print(label, type(e).__name__, e)


show("walrus_filter([0, 1, 2])", lambda: walrus_filter([0, 1, 2]))
show("walrus_filter([1, 0])", lambda: walrus_filter([1, 0]))
show("walrus_filter([])", lambda: walrus_filter([]))
show("walrus_key([1, 2])", lambda: walrus_key([1, 2]))
show("walrus_key([1, 1])", lambda: walrus_key([1, 1]))

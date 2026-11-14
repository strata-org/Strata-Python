# The comprehensions of p51_comp_clauses, called: clauses and parts that no other program runs:
# - an `if` between two `for`s, and an `if` after a later `for`;
# - a filter that reads the variable of a later `for` clause: before that clause first runs,
#   the read raises UnboundLocalError; after it runs, the read sees the value the clause left;
# - a walrus in a function's comprehension that a later part of the comprehension reads;
# - attribute and subscript targets;
# - set and dict elements that are unhashable (a list);
# - an element, a key and a value whose lowering spans several blocks;
# - a comprehension in a filter, and one in a later `for`'s iterable;
# - a comprehension in a `try` body;
# - len of a comprehension.
def between(xs, ys):
    return [(x, y) for x in xs if x for y in ys]


def later_if(xs, ys):
    return [(x, y) for x in xs for y in ys if x < y]


def later(xs, ys):
    return [x for x in xs if x == 0 or y for y in ys]


def later_unbound(xs, ys):
    return [x for x in xs if y for y in ys]


def walrus_filter(xs):
    return [y for x in xs if (y := x * 10)]


def walrus_key(xs):
    return {(k := x * 10): k + 1 for x in xs}


def targets(o, d, xs):
    a = [o.a for o.a in xs]
    b = [d["k"] for d["k"] in xs]
    return a, b


def unhashable_set(xs):
    return {[x] for x in xs}


def unhashable_dict(xs):
    return {[x]: x for x in xs}


def blocks(xs, d):
    a = [x if x else -x for x in xs]
    b = {(x and d): (x or d) for x in xs}
    return a, b


def nested(xss):
    a = [xs for xs in xss if [x for x in xs if x]]
    b = [y for xs in xss for y in [x * 2 for x in xs]]
    return a, b


def lengths(xs):
    return len({x for x in xs}), len([x * 2 for x in xs])


def in_try(xs):
    try:
        return [1 // x for x in xs]
    except ZeroDivisionError:
        return None


class O:
    pass


def show(label, f):
    try:
        print(label, f())
    except Exception as e:
        print(label, type(e).__name__, e)


show("between", lambda: between([0, 1, 2], [5, 6]))
show("later_if", lambda: later_if([1, 2, 3], [2, 3]))
show("later", lambda: later([0, 1, 2], [7]))
show("later_unbound", lambda: later_unbound([1, 2], [3]))
show("walrus_filter", lambda: walrus_filter([0, 1, 2]))
show("walrus_key", lambda: walrus_key([1, 2]))
o = O()
d = {}
show("targets", lambda: targets(o, d, [1, 2, 3]))
print(o.a, d)
show("unhashable_set", lambda: unhashable_set([1]))
show("unhashable_dict", lambda: unhashable_dict([1]))
show("blocks", lambda: blocks([1, 0, -2], 5))
show("nested", lambda: nested([[0, 0], [1, 0], []]))
show("in_try", lambda: in_try([1, 0]))
show("in_try2", lambda: in_try([1, 2]))
show("lengths", lambda: lengths([1, 2, 2]))

# Name binding for `pymantle features`.  Every name read here is bound except those marked
# UNBOUND, which `FeatureUsageTest.lean` expects to be exactly the unresolved names.
import os.path
import a.b.c as abc
from collections import OrderedDict as OD


def deco(*args, **kwargs):
    return lambda fn: fn


DEFAULT = 1
KW_DEFAULT = 2


class Base:
    pass


class Meta:
    pass


# Lambda parameters, walrus targets, comprehension, `for` and `with` targets, match captures,
# and defaults, decorator arguments and class bases read from the enclosing scope.
@deco(DEFAULT, key=KW_DEFAULT)
def f(p, q=DEFAULT, *rest, k=KW_DEFAULT, **kw):
    g = lambda x, y=p, *a, z, **b: (x, y, z, a, b)
    if (n := p) > 0:
        pass
    pairs = [(x, y, zs) for x, (y, *zs) in rest if zs]
    names = {k2: v for k2, v in kw.items()}
    seen = [(last := x) for x in rest]
    match p:
        case [h, *t]:
            pass
        case {"k": mv, **others}:
            pass
        case Base(attr=cap) as whole:
            pass
    for i, (j, *js) in rest:
        pass
    with q as (w1, w2), q as [w3, *w4]:
        pass
    return (g, n, pairs, names, seen, last, h, t, mv, others, cap, whole, i, j, js,
            w1, w2, w3, w4, k, os.path, abc, OD)


class C(Base, metaclass=Meta):
    attr = 1
    xs = [attr]
    # The class body evaluates the outermost iterable and the defaults.
    ys = [x for x in xs]

    def m(self, d=attr):
        return self.attr, d

    def bare(self):
        return attr  # UNBOUND: class names are invisible to methods

    zs = [x + attr for x in xs]  # UNBOUND: and to comprehensions


def set_g():
    global G
    G = 1


def get_g():
    return G


def uses_undefined():
    return undefined_name  # UNBOUND


@undefined_decorator(undefined_decorator_arg)  # UNBOUND x2
def h(x=undefined_default, *, y=undefined_kw_default):  # UNBOUND x2
    return x, y


class D(UndefinedBase, metaclass=UndefinedMeta):  # UNBOUND x2
    pass


lam = lambda: undefined_in_lambda  # UNBOUND

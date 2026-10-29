# `from a.b import x` binds `x` to `a.b.x`; `as y` binds `y` instead.
from os.path import join
from os.path import basename as base
from collections import OrderedDict, defaultdict as dd


def f(p):
    return join(p, base(p)), OrderedDict(), dd(list)

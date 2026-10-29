# Relative imports are rejected; the names they bind are still classified.
from . import sibling
from ..pkg.mod import thing as t
from .mod import other


def f():
    return sibling, t, other

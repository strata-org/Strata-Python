# A ghost's `type=` sees the binding in scope at its declaration site: the
# import rebinds the alias before the ghost reads it.
MyType = int
from typing import Any as MyType
ghost(name="g", type=MyType)

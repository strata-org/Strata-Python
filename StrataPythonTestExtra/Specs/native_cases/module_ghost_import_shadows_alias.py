# A name that a typing import binds is also bound by an assignment, so PySpec rejects the
# model: it would read MyType only as the typing import.
MyType = int
from typing import Any as MyType
ghost(name="g", type=MyType)

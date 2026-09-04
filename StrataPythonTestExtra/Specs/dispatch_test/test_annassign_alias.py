from typing import Any

import servicelib


def factory():
    sl: Any = servicelib
    return sl.connect("storage")

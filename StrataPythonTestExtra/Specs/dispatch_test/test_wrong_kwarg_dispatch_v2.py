from typing import Any

import servicelib


def bad_kwarg() -> Any:
    return servicelib.connect(flavor="storage")

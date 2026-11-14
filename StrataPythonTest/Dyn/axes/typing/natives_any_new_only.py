from typing import Any
try:
    Any()
except TypeError as e:
    print(type(e).__name__, e)

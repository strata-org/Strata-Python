from typing import Optional, Union
for f in (lambda: Optional | int, lambda: int | Union):
    try:
        print(repr(f()))
    except Exception as e:
        print(type(e).__name__, e)

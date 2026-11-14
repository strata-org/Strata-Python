from typing import Union
try:
    class C(Union):
        pass
except Exception as e:
    print(type(e).__name__, e)

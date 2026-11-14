from typing import Any
try:
    Any()
except Exception as e:
    print(type(e).__name__, e)
class C(Any):
    def __repr__(self):
        return 'C()'
print(C())

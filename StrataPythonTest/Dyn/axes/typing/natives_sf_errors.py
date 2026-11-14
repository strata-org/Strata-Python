from typing import Optional, Union
for f in (lambda: Union(), lambda: isinstance(1, Optional), lambda: issubclass(int, Union), lambda: Optional.__name__, lambda: Optional.foo):
    try:
        print(f())
    except Exception as e:
        print(type(e).__name__, e)
try:
    class C(Union):
        pass
except Exception as e:
    print(type(e).__name__, e)

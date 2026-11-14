from typing import Optional, Union
for f in (lambda: Union(), lambda: isinstance(1, Optional), lambda: issubclass(int, Union), lambda: Optional.__name__):
    try:
        print(f())
    except Exception as e:
        print(type(e).__name__, e)

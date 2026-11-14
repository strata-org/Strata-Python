from typing import List, Union
for f in (lambda: issubclass(list, List[int]), lambda: issubclass(int, Union[int, str])):
    try:
        print(f())
    except Exception as e:
        print(type(e).__name__, e)

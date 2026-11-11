from typing import Optional
fr = Optional["N"].__args__[0]
print(fr, fr.__forward_arg__, fr.__forward_module__, fr == Optional["N"].__args__[0])
print(hasattr(fr, "__forward_code__"))

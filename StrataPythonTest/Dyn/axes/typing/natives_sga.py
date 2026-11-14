from typing import List, Dict, Tuple
print(repr(List), repr(Dict), repr(Tuple))
print(isinstance([], List), isinstance({}, List), issubclass(list, List), issubclass(dict, Dict), isinstance((1,), Tuple))
print(repr(List | None), repr(None | Dict))

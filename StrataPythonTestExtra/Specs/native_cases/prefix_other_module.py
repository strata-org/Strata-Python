# A subscript through another module than typing is an error, even where the module name
# was rebound after an import that PySpec reads, such as import builtins.
import builtins as m
m = 0


def f(x: m.dict[str, int]) -> None:
    ...

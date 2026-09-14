# One cell holding two shapes: a dict with int and str values, or a list with
# bool and int elements. A read then forks per receiver tag, and the index type
# decides which branch can complete at all. CPython, for the four combinations:
#   read_by_name(True)  = 1          read_by_name(False)  raises TypeError
#   read_by_index(True) raises KeyError   read_by_index(False) = True
def build(flag: bool) -> object:
    if flag:
        inner = {"a": 1, "b": "s"}
    else:
        inner = [True, 2]
    box = {"c": inner}
    return box["c"]


def read_by_name(flag: bool) -> object:
    return build(flag)["a"]


def read_by_index(flag: bool) -> object:
    return build(flag)[0]

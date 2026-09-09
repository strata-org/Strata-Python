# NAIVE MODEL WOULD GET WRONG: evaluates target before RHS for subscript store
trace = []
class Obj:
    def __setitem__(self, k, v): trace.append(f"store[{k}]={v}")
def get_obj(): trace.append("obj"); return Obj()
def get_key(): trace.append("key"); return 0
def get_val(): trace.append("val"); return 99
get_obj()[get_key()] = get_val()
# Naive (target first): obj, key, val. CPython: val, obj, key
assert trace == ["val", "obj", "key", "store[0]=99"]
print("BOUNDARY: naive model evaluates target first; CPython evaluates RHS first")

# NAIVE MODEL WOULD GET WRONG: assumes closure captures value at definition time
def make_funcs():
    funcs = []
    for i in range(3):
        funcs.append(lambda: i)  # naive: captures i=0,1,2. CPython: all share cell
    return funcs
results = [f() for f in make_funcs()]
assert results == [2, 2, 2], f"Got {results}"
print("BOUNDARY: naive value-capture model gives [0,1,2]; CPython gives [2,2,2]")

from pyhard import loop_invariant, OLD

def find(xs, v):
    loop_invariant(lambda: True)
    for i in range(len(xs)):
        if xs[i] == v:
            return i
    return -1

print(find([3, 4, 5], 4))

from pyhard import loop_invariant, OLD

class Box:
    pass

def f(xs):
    b = Box()
    b.x = 0
    loop_invariant(lambda: True)
    for b.x in xs:
        pass
    return b.x

print(f([7, 8]))

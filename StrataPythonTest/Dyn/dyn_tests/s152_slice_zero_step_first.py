# A zero slice step raises ValueError right after the step is converted, before the start and
# the stop: their conversion doesn't run.
for seq in ([1, 2, 3], (1, 2, 3), "abc"):
    try:
        seq[None:'a':0]
    except ValueError:
        print("ValueError")
    except TypeError:
        print("TypeError")

class A:
    def __index__(self):
        print("A")
        return 0
xs = [1, 2, 3]
try:
    xs[A()::0]
except ValueError:
    print("ValueError")
try:
    del xs[A()::0]
except ValueError:
    print("ValueError")
try:
    xs[A()::0] = [1]
except ValueError:
    print("ValueError")
print(len(xs))

# With a step that isn't zero, the step is converted first, then the start and the stop.
class P:
    def __init__(self, name, v):
        self.name = name
        self.v = v

    def __index__(self):
        print(self.name)
        return self.v
print(xs[P("start", 0):P("stop", 2):P("step", 1)][0])

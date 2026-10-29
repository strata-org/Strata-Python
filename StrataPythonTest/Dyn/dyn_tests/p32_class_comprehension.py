# A comprehension in a class body cannot see the class's names, except the outermost
# iterable, which the class body evaluates.  Its iteration variable is listed with the
# class's names.
class C:
    xs = [1, 2]
    k = 3
    ys = [x + k for x in xs]

from pyhard import loop_invariant


# The invariant holds at the loop's head, before the next element is taken. There, `x` is the
# previous element, and it is unbound at the first entry, so this invariant is false there: an
# invariant can't speak of the current element.
def f(xs):
    n = 0
    loop_invariant(lambda: x in xs)
    for x in xs:
        n += 1
    return n


print(f([1, 2]))

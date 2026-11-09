# The items of a slice assignment come from a user iterable whose __iter__ grows the list.
# CPython fits the slice to the list's size after reading them; the model stops with a gap
# before that, when it walks the iterable inside the operation.
class G:
    def __iter__(self):
        xs[4:] = [0]
        return iter([7, 8])
xs = [1, 2, 3, 4]
xs[-3:-1] = G()
print(len(xs), xs[1], xs[2])

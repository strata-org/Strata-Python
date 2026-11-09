# Test: a for loop over an object whose class loses __getitem__ while it is iterated
class G:
    def __getitem__(self, i):
        del G.__getitem__
        return i
try:
    for x in G():
        pass
except TypeError as e:
    msg = e.args[0]

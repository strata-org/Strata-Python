# Test: x in s, where x is a set, compares the members with a frozenset copy of x
class K:
    def __hash__(self):
        # hash(frozenset()) in CPython 3.12
        return 133146708735736
    def __eq__(self, other):
        global seen
        seen = type(other).__name__
        return True
seen = None
s = {K()}
x = {1} & {2}
r = x in s

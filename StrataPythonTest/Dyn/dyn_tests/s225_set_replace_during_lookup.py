# Test: a lookup in a set whose __eq__ replaces the set's table with &= sees the change
class X:
    def __hash__(self):
        return 1
    def __eq__(self, other):
        global calls
        calls += 1
        s.__iand__(t)
        return False
calls = 0
nine = 9
one = 1
s = {nine, one}
t = {one, nine}
r = X() in s

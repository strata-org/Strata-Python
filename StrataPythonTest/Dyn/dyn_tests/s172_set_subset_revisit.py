# Test: a subset test looks each member up, so it may compare a member several times too
n = 0
class Q:
    def __hash__(self):
        return -2
    def __eq__(self, o):
        global n
        n += 1
        return False
print({Q()} <= {"a", "b", "c", -2}, n)

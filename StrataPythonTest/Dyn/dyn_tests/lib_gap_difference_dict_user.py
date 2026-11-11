# A set difference with a dict, when the set's members are user objects whose comparisons may
# run user code, stops with a gap.
class U:
    def __hash__(self):
        return 1

    def __eq__(self, other):
        return False


print(len(set([U(), U()]).difference({1: 0, 2: 0})))

# Test: a set update whose __eq__ removes a member and adds an equal new one back
z = 0
calls = 0
class K:
    def __hash__(self):
        return 512
    def __eq__(self, other):
        global calls, s
        calls += 1
        print("eq", calls)
        if calls == 1:
            s -= {2 ** 70 + z}
            s |= {2 ** 70 + z}
        return False
s = {2 ** 70 + z, z}
s |= {K(), z}
print(len(s))

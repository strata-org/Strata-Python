# Test: != on objects that define only __eq__ calls __eq__ once and inverts its result
n = 0
class C:
    def __eq__(self, o):
        global n
        n = n + 1
        return True
print(C() != C(), n)

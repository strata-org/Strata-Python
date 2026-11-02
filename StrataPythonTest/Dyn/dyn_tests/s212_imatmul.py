# Test: `@=` tries __imatmul__ first, then __matmul__
class M:
    def __imatmul__(self, o):
        return "imm"
    def __matmul__(self, o):
        return "mm"
class N:
    def __imatmul__(self, o):
        return NotImplemented
    def __matmul__(self, o):
        return "mm"
class O:
    def __imatmul__(self, o):
        return "only imm"
m = M()
m @= 3
n = N()
n @= 3
o = O()
o @= 3
print(m, n, o)

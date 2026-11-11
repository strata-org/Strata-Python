# A __getitem__ iterator that its own __getitem__ or __len__ steps or ends re-entrantly.
class A:
    depth = 0
    def __getitem__(self, i):
        if A.depth == 0:
            A.depth = 1
            try:
                next(A.it)
            except StopIteration:
                pass
            A.depth = 2
            return "outer"
        if A.depth == 1:
            raise IndexError
        return i
A.it = iter(A())
print(next(A.it, "end"))
print(next(A.it, "end"))

class B:
    rec = False
    def __getitem__(self, i):
        if not B.rec and i == 0:
            B.rec = True
            print("inner", next(B.it))
            return "outer0"
        if i >= 4:
            raise IndexError
        return i
B.it = iter(B())
for x in B.it:
    print(x)

class C:
    def __getitem__(self, i):
        if i >= 5:
            raise IndexError
        return i
    def __len__(self):
        next(C.it)
        return 5
C.it = iter(C())
print(C.it.__length_hint__())


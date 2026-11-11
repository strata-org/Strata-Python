# A callable iterator whose call exhausts it re-entrantly: next() raises StopIteration, and the
# sentinel's __eq__ doesn't run on the dropped result.
class S:
    rec = False
def spam():
    if S.rec:
        return 2
    S.rec = True
    for _ in S.it:
        pass
    return 1
S.it = iter(spam, 2)
try:
    print(next(S.it))
except StopIteration:
    print("StopIteration")

class Sent:
    def __eq__(self, o):
        print("sentinel eq", o)
        return o == 2
class T:
    rec = False
def eggs():
    if T.rec:
        return 2
    T.rec = True
    for _ in T.it:
        pass
    return 1
T.it = iter(eggs, Sent())
print(next(T.it, "end"))
print(next(T.it, "end"))

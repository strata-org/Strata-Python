# str.translate with a logging table (the ASCII cache, the end of the fast path, the slow path's
# second lookups after a deletion), and its errors.
class M:
    def __init__(self, d):
        self.d = d

    def __getitem__(self, k):
        print("get", k)
        return self.d[k]


def show(f, *args):
    try:
        print(repr(f(*args)))
    except (TypeError, ValueError, OverflowError) as e:
        print(type(e).__name__, e.args[0])


print("aab".translate(M({97: "x"})))
print("abcab".translate(M({97: None, 98: "yy"})))
print("abca".translate(M({98: 233})))
print("aXbYa".translate(M({88: None, 89: None, 98: "é"})))
print("éaé".translate(M({233: None, 97: "z"})))
print("éaab".translate(M({233: None, 97: None})))
print("hello".translate({104: "J", 108: None}), "abc".translate({}))
show("abc".translate, 1)
show("abc".translate, {97: 1.5})
show("abc".translate, {97: 0x110000})
show("abc".translate, {97: -1})
show("abc".translate, {97: 2 ** 70})
show("abc".translate, [])

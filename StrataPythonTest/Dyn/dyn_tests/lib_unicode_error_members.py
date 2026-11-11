# The five members of UnicodeEncodeError and UnicodeDecodeError as CPython 3.12 reads them: None
# and 0 until __init__ sets them, start and end set as they parse, and the object fields only
# once all five arguments parse.
# 1. __new__ only: object fields None, start/end 0
e = UnicodeEncodeError.__new__(UnicodeEncodeError)
print("new-only", e.encoding, e.object, e.start, e.end, e.reason)
d = BaseException.__new__(UnicodeDecodeError)
print("base-new", d.encoding, d.object, d.start, d.end, d.reason)
# 2. subclass whose __init__ swallows a failed parse partway (start parsed, end bad)
class E(UnicodeEncodeError):
    def __init__(self, *a):
        try: super().__init__(*a)
        except TypeError as x: print("  init raised:", x)
e = E("a", "b", 5, "x", "r")
print("partial-encode", e.encoding, e.object, e.start, e.end, e.reason)
# 3. decode: object not bytes-like, fails after the parse
class D(UnicodeDecodeError):
    def __init__(self, *a):
        try: super().__init__(*a)
        except TypeError as x: print("  init raised:", x)
d = D("a", 5, 1, 2, "r")
print("decode-bad-object", d.encoding, d.object, d.start, d.end, d.reason)
# 4. re-init that fails on the count clears the object fields
e = UnicodeEncodeError("a", "b", 1, 2, "r")
try: e.__init__(1)
except TypeError as x: print("  reinit raised:", x)
print("reinit-fail", e.encoding, e.object, e.start, e.end, e.reason)
# 5. normal
e = UnicodeEncodeError("ascii", "\xe9", 0, 1, "ordinal not in range(128)")
print("normal", repr(e.encoding), repr(e.object), e.start, e.end, repr(e.reason), str(e))
try: "\xe9".encode("ascii")
except UnicodeEncodeError as x: print("codec", x.encoding, repr(x.object), x.start, x.end, x.reason)

e = UnicodeEncodeError("a", "b", 1, 2, "r")
try: e.__init__(1)
except TypeError: pass
print(repr(str(e)), e.args)
class E(UnicodeEncodeError):
    def __init__(self, *a):
        try: super().__init__(*a)
        except TypeError: pass
e = E("a", "bcdefgh", 5, "x", "r")
print(repr(str(e)))

# User code in a later conversion sees the fields that already parsed.
class I:
    def __index__(self):
        print(e.encoding, e.object, e.reason)
        return 0


e = ValueError.__new__(UnicodeEncodeError)
e.__init__("ascii", "x", I(), 1, "r")
print(e.start, e.end, e.reason)
e = ValueError.__new__(UnicodeDecodeError)
e.__init__("ascii", b"x", I(), 1, "r")


# str(e) while __init__ runs: a field that isn't set yet is written as <NULL>.
class J:
    def __index__(self):
        print(str(e))
        return 0


e = ValueError.__new__(UnicodeEncodeError)
e.__init__("ascii", "x", J(), 1, "r")
e = ValueError.__new__(UnicodeDecodeError)
e.__init__("ascii", b"x", J(), 1, "r")

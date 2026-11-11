# UnicodeEncodeError and UnicodeDecodeError: built by a program (the argument checks) or raised by
# a codec (str.encode, str(b, encoding), bytes(s, encoding)), and str(e) from their fields.
for a in [(), ("a",), (1, "x", 0, 1, "r"), ("a", 1, 0, 1, "r"), ("a", "x", "y", 1, "r"), ("a", "x", 0, 1, 2), ("a","x",2**70,1,"r")]:
    try: UnicodeEncodeError(*a)
    except Exception as e: print(type(e).__name__, e)
for a in [("a", 1, 0, 1, "r"), ("a", b"x", 0, 1, "r"), ("a", "x", 0, 1, "r")]:
    try: e = UnicodeDecodeError(*a); print(str(e))
    except Exception as e: print(type(e).__name__, e)
try: UnicodeEncodeError("a", "x", 0, 1, "r", x=1)
except Exception as e: print(type(e).__name__, e)
e = UnicodeEncodeError("ascii", "aé", 1, 2, "bad"); print(str(e), e.args)
e = UnicodeEncodeError("ascii", "aé", -1, 5, "bad"); print(str(e))
e = UnicodeDecodeError("utf-8", b"\xff\xfe", 0, 1, "bad"); print(str(e))
e = UnicodeDecodeError("utf-8", b"\xff\xfe", 0, 2, "bad"); print(str(e))
try: "é".encode("ascii")
except UnicodeEncodeError as e: print(str(e), e.args)
try: str(b"\xff", "utf-8")
except UnicodeDecodeError as e: print(str(e), e.args)
try: str(b"a\xffb", "ascii")
except UnicodeError as e: print(type(e).__name__, str(e))
try: bytes("é", "ascii")
except UnicodeError as e: print(type(e).__name__, str(e))
class U(UnicodeEncodeError): pass
print(str(U("x", "yy", 0, 2, "z")))
for a in [("utf-8", 5, "x", 1, "r"), ("utf-8", 5, 1, 2, 3), ("utf-8", 5, 1, 2, "r")]:
    try: UnicodeDecodeError(*a)
    except TypeError as e: print(e)


class SE(str):
    def __repr__(self):
        return "SE!"


try: SE("é").encode("ascii")
except UnicodeEncodeError as e: print(e.args)
try: bytes(SE("é"), "ascii")
except UnicodeEncodeError as e: print(e.args)
print("é".encode(), "é".encode("latin-1"), "aé".encode("ascii", "replace"), "x".encode(errors="strict"))
for a in [(1,), ("utf-8", 1), ("nope",), ("utf-8", "nope")]:
    try: "é".encode(*a)
    except Exception as e: print(type(e).__name__, e)

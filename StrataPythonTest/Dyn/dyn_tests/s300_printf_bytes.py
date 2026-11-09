# Test: printf-style % of a bytes format, __bytes__, __index__, __int__ and __float__, and a plain right operand's __rmod__
def t(fmt, args):
    try:
        r = fmt % args
        print(repr(r))
    except Exception as e:
        print(type(e).__name__, e)
t(b"%s %b", (b"x", b"yz"))
t(b"%d %5.2f %c %c", (3, 1.5, 65, b"q"))
t(b"%s", "str")
t(b"%r %a", ("é", "é"))
t(b"%(k)s", {b"k": b"v"})
t(b"%i", "x")
t(b"%f", "x")
t(b"%c", 300)
t(b"%x %#X", (255, 255))
class B:
    def __bytes__(self):
        return b"BB"
t(b"%s", B())
class I:
    def __index__(self):
        return 9
t("%x %d %c", (I(), I(), I()))
class N:
    def __int__(self):
        return 12
t("%d", N())
t("%x", N())
class F:
    def __float__(self):
        return 2.5
t("%f", F())
t("%d", F())
class P:
    def __rmod__(self, o):
        return "rmod"
t("x", P())

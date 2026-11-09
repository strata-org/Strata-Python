# Test: printf-style % edge cases: %= on a str, a %% after a key, mapping and argument counts, padding, huge ints, inf and nan
def t(fmt, args):
    try:
        r = fmt % args
        print(repr(r))
    except Exception as e:
        print(type(e).__name__, e)
x = "a"
x %= ()
print(x)
t("%(a)%", {"a": 1})
t("%s", {"a": 1})
t("", {})
t("", 5)
t("%-08.3f|%+08d|%#o", (-3.5, 5, 0))
t("%e", 10**400)
t("%d", 10**5000)
t("%x", -255)
t("%#x", -255)
t("%c", -1)
t("% 5d|%+5d|%- 5d|", (3, 3, 3))
t("%s %s %s", [1, 2, 3])
t("%G %g", (1e308 * 10, 1e308 * 10 - 1e308 * 10))
class R:
    def __repr__(self):
        return "R!"
t("%r|%s|%a|%10r|", (R(), R(), R(), R()))

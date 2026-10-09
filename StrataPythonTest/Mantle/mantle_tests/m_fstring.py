# f-strings, as CPython's `FORMAT_VALUE` and `BUILD_STRING`: a field evaluates its value,
# then its format spec, then applies `!s`/`!r`/`!a`, then formats, without looking up the
# builtins `str`, `repr`, `ascii` or `format`.  So `f"{x!r:{y}}"` reads `y` before it calls
# `repr(x)`.  A lone part is not concatenated.
e = f""
c = f"abc"
s1 = f"{x}"
s2 = f"a{x}b"
s3 = f"{x!s}{x!r}{x!a}"
s4 = f"{x:>10}"
s5 = f"{x!r:{y}}"
s6 = f"{x=}"
s7 = f"{x:{w}.{p}}"
s8 = "p" f"{x}" "q"
s9 = f"{f'{x}'}"
s10 = f"{x=:>3}"
s11 = f"{x:}"

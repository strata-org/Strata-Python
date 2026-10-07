# Constant defaults are materialized in the prologue; each is indistinguishable
# from definition-time evaluation because there is no scope to capture.
#
# KNOWN DIVERGENCE (unrelated to argument binding): the interpreter renders a
# float as "1.500000" where CPython prints "1.5". That is Machine.render using
# Lean's default Float formatting instead of shortest round-trip repr.
def c(a, b=None, n=3, s="x", f=1.5, t=True):
    print(a, b, n, s, f, t)
c(1)
c(1, 2)
c(1, n=9)
c(1, t=False)

def kwd(a, *, k=7):
    print(a, k)
kwd(1)
kwd(1, k=2)

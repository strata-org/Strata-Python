# Globals and builtins are looked up at run time: a builtin added at run time is found.
import builtins

builtins.log = print
log("hi")


def f():
    return log


# `later` is assigned after the `def`; `missing` is neither a global nor a builtin.
def g():
    return later, missing


later = 1

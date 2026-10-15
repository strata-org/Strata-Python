# CPython reports its symbol table's errors, those of the walk and then those of the analysis,
# before its compiler's, even one on an earlier line.
break
def f(a, a):
    pass
def g():
    nonlocal x

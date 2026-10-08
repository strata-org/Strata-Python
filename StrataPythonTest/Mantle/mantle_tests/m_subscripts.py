# Attributes, subscripts and slices, evaluated left to right as CPython does.  A slice that
# is the whole subscript is `getSlice`; one inside a tuple is `mkSlice`, then `getItem`.
x = o.a
y = o.a.b
z = o.m(a)
i = o[k]
s1 = o[a:b]
s2 = o[a:b:c]
s3 = o[::]
s4 = o[:b]
s5 = o[a:b, c]
s6 = o[a, b]

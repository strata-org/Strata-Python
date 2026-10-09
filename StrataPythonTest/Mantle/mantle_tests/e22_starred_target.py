# CPython's compiler rejects a starred target outside a tuple or list, in every kind of
# target.
*a = v
for *a in v: pass
with v as *a: pass
[0 for *a in v]

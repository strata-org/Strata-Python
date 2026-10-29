# CPython's compiler rejects two starred elements in one target, at any depth.
a, *b, *c = v
a, *(*b, *c) = v
for a, *b, *c in v: pass

# A condition lowers to branches, as CPython's `compiler_jump_if` does: each operand's
# `__bool__` runs at most once.  As a value, `and`/`or` test each operand but the last, and
# produce the first that decides the result, or the last; `x if c else y` tests `c` as a
# condition.
if a and b:
    r = 1
if a or b:
    r = 2
if not a:
    r = 3
if (a and b) or c:
    r = 4
if a if b else c:
    r = 5
if a < b < c:
    r = 6
if a < b < c < d:
    r = 7
if not (a and b):
    r = 8
if not (a < b < c):
    r = 9
if (a if b else c) if d else e:
    r = 10
while a and not b:
    r = 11
while a or b:
    r = 12
else:
    r = 13
v = a and b or c
w = a if b and c else b
u = a or b or c

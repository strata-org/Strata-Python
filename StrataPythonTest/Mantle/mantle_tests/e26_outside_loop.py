# `break` and `continue` where an enclosing loop does not count: in a nested def or class
# body, and in the loop's own `else`.
for x in []:
    def g():
        continue
    class C:
        break
else:
    break
while x:
    pass
else:
    continue

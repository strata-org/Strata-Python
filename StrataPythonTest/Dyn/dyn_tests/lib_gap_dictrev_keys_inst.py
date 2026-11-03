# The same over an instance dict.
class C:
    pass


c = C()
c.x = 0
c.y = 0
c.z = 0
it = reversed(c.__dict__)
print(next(it))
del c.__dict__["y"]
c.__dict__["w"] = 0
for k in it:
    print(k)

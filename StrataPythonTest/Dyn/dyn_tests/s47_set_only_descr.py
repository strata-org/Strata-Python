# Test: a read finds the instance dict entry before a class descriptor that has __set__ but no __get__
class D:
    def __set__(self, o, v):
        print("set")
class C:
    x = D()
c = C()
c.__dict__["x"] = 5
print(c.x == 5)

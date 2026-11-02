# Test: classmethod and staticmethod objects: their __init__, what they copy from the callable, and their __dict__
class S(staticmethod):
    def __init__(self, f):
        super().__init__(lambda: 1)
class A:
    m = S(5)
print(A.m())
def f():
    pass
s = staticmethod(f)
print(s.__name__, s.__module__)
cm = classmethod(f)
cm.tag = 1
print(cm.tag)
class K:
    def __call__(self):
        pass
    @property
    def __name__(self):
        print("name read")
        return "k"
print(staticmethod(K()).__name__)
class G:
    def __call__(self, o):
        return 3
    @property
    def __doc__(self):
        print("doc read")
        return "gdoc"
class B:
    x = property(G())
print(B().x)
s.__qualname__

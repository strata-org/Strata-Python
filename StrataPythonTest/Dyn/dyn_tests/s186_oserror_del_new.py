# Test: deleting an OSError subclass's own __new__, after which CPython's tp_new is still slot_tp_new
class O(OSError):
    def __new__(cls, *a):
        return super().__new__(cls, *a)
    def __init__(self, *a):
        pass
del O.__new__
o = O(2, "no such")
print(o.errno, o.strerror, len(o.args))

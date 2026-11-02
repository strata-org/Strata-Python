# Test: object.__init__ with excess arguments on a type that makes no instances, whose tp_new isn't object's
print(object.__init__(len, 1))

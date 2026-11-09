# Test: a __format__ taken from str by another class raises CPython's TypeError for an empty spec
class E(Exception):
    __format__ = str.__format__
try:
    print(f"{E('msg')}", "|", "%s" % (E('m2'),))
except TypeError as e:
    print("TypeError", e)

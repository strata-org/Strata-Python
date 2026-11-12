# A mappingproxy's comparison forwards to its dict, so CPython's == of a class's __dict__ and an
# object whose __eq__ accepts a dict is True; the model doesn't follow that forwarding, so the run
# stops with a gap.
class C:
    pass
class E:
    def __eq__(self, o):
        return type(o) is dict
print(C.__dict__ == E())

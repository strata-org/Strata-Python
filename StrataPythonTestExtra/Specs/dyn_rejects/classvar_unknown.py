# A class variable whose value the model doesn't define rejects the model: the module body
# would raise.
class C:
    X = Missing

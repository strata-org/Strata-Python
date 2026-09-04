import servicelib

xs = [1, 2, 3]
for servicelib in xs:
    pass


def use_it():
    return servicelib.connect("storage")

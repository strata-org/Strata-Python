import servicelib

with open("data.txt") as servicelib:
    pass


def use_it():
    return servicelib.connect("storage")

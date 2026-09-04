import servicelib

data = ("a", "b")
match data:
    case (servicelib, _):
        pass
    case _:
        pass


def use_it():
    return servicelib.connect("storage")

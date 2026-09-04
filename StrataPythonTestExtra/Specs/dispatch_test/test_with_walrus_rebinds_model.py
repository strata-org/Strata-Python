from servicelib.Contract import modeled_text

with open((modeled_text := "f")) as fh:
    pass


def use_it():
    return modeled_text("")

from servicelib.Contract import modeled_text


def f(x: (modeled_text := int)):
    return x


def use_it():
    return modeled_text("")

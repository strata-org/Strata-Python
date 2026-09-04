from servicelib.Contract import modeled_text


class C((modeled_text := str)):
    pass


def use_it():
    return modeled_text("")

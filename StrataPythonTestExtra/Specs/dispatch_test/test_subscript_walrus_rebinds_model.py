from servicelib.Contract import modeled_text

values = {}
values[(modeled_text := 0)] = 1


def use_it():
    return modeled_text("")

from servicelib.Contract import modeled_text

unused = (modeled_text := 42)


def use_it():
    return modeled_text("")

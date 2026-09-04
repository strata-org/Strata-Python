from servicelib.Contract import modeled_text

x = ((modeled_text := 42), modeled_text(""))


def use_it():
    return x

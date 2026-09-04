from servicelib.Contract import modeled_text

try:
    raise ValueError
except (modeled_text := ValueError):
    pass


def use_it():
    return modeled_text("")

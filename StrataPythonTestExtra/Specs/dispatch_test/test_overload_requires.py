import overload_requires


def connect_short_name() -> None:
    c = overload_requires.connect("s")
    c.go()

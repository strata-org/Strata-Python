class Box:
    def __init__(self):
        self.value = "initial"


class BuiltError(Exception):
    def __init__(self, box: Box):
        box.value = "exception-initialized"


def construct_before_raise() -> str:
    box = Box()
    try:
        raise BuiltError(box)
    except BuiltError:
        return box.value


result = construct_before_raise()

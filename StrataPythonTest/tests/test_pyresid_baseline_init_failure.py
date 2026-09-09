class Box:
    def __init__(self):
        self.value = "initial"


class Failing:
    def __init__(self, box: Box):
        box.value = "init-evaluated"
        raise LookupError()


def late_step(box: Box) -> None:
    box.value = "late-step"
    return None


def construct() -> str:
    box = Box()
    try:
        value = Failing(box)
        late_step(box)
        return "missed-init-error"
    except LookupError:
        return box.value


result = construct()

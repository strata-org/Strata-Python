class Box:
    def __init__(self):
        self.value = "initial"


def fail_target(box: Box) -> list[int]:
    box.value = "target-evaluated"
    raise LookupError()


def late_index(box: Box) -> int:
    box.value = "index-evaluated"
    return 0


def store() -> str:
    box = Box()
    try:
        fail_target(box)[late_index(box)] = 1
        return "missed-target-error"
    except LookupError:
        return box.value


result = store()

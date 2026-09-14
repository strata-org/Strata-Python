class Box:
    def __init__(self):
        self.value = "initial"


def fail_key(box: Box):
    box.value = "key-evaluated"
    raise LookupError()


def late_value(box: Box) -> int:
    box.value = "value-evaluated"
    return 1


def build() -> str:
    box = Box()
    try:
        payload = {fail_key(box): late_value(box)}
        return "missed-key-error"
    except LookupError:
        return box.value


result = build()

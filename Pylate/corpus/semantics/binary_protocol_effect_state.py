class Box:
    def __init__(self):
        self.value = 0


class IterMutator:
    def __init__(self, box: Box):
        self.box = box

    def __iter__(self):
        self.box.value = "iterated"
        return [[1]]


class GetItemMutator:
    def __init__(self, box: Box):
        self.box = box

    def __getitem__(self, index: int):
        self.box.value = "indexed"
        return [index]


class ExhaustingGetItem:
    def __init__(self, box: Box):
        self.box = box

    def __getitem__(self, index: int):
        self.box.value = "exhausted"
        raise IndexError()


class RaisingGetItem:
    def __init__(self, box: Box):
        self.box = box

    def __getitem__(self, index: int):
        self.box.value = "failed"
        raise LookupError()


def state_after_iter_error() -> str:
    box = Box()
    try:
        {"key": 1}.keys() & IterMutator(box)
    except TypeError:
        return box.value
    return "normal"


def state_after_getitem_error() -> str:
    box = Box()
    try:
        {"key": 1}.keys() & GetItemMutator(box)
    except TypeError:
        return box.value
    return "normal"


def state_after_getitem_exhaustion() -> str:
    box = Box()
    {"key": 1}.keys() & ExhaustingGetItem(box)
    return box.value


def state_after_getitem_failure() -> str:
    box = Box()
    try:
        {"key": 1}.keys() & RaisingGetItem(box)
    except LookupError:
        return box.value
    return "normal"


iter_result = state_after_iter_error()
getitem_result = state_after_getitem_error()
exhaustion_result = state_after_getitem_exhaustion()
failure_result = state_after_getitem_failure()

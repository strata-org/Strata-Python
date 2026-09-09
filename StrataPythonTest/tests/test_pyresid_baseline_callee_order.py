class Box:
    def __init__(self):
        self.value = "initial"


class Worker:
    def echo(self, value):
        return value


def make_worker(box: Box) -> Worker:
    box.value = "receiver-evaluated"
    return Worker()


def identity(value):
    return value


def choose_callable(box: Box):
    box.value = "callee-evaluated"
    return identity


def method_order() -> str:
    box = Box()
    return make_worker(box).echo(box.value)


def generic_order() -> str:
    box = Box()
    return choose_callable(box)(box.value)


method_result = method_order()
generic_result = generic_order()

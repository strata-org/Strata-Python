class A:
    def only_a(self) -> bool:
        return True


class B:
    def only_b(self) -> int:
        return 5


def choose(flag: bool) -> bool | int:
    if flag:
        value = A()
    else:
        value = B()

    if flag:
        return value.only_a()
    return value.only_b()

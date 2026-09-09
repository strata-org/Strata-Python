class A:
    def marker(self) -> int:
        return 1


class B:
    def marker(self) -> int:
        return 2


def reassigned_guard(flag: bool) -> int:
    if flag:
        value = A()
    else:
        value = B()

    flag = not flag
    if flag:
        return value.marker()
    return value.marker()


def unchanged_guard(flag: bool) -> int:
    if flag:
        value = A()
    else:
        value = B()

    other = not flag
    if flag:
        return value.marker()
    return value.marker()


def killed_difference(flag: bool) -> int:
    if flag:
        value = 1
    else:
        value = "old"

    value = 0
    return value + 1


def finite_loop(flag: bool) -> bool:
    while flag:
        flag = not flag
    return flag

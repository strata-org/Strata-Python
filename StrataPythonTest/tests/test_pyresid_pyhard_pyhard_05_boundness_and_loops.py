def conditional(flag: bool) -> int:
    if flag:
        value = 10
    return value


def loop_assignment(flag: bool) -> int:
    while flag:
        result = 1
        flag = False
    return result


def both_branches(flag: bool) -> int:
    if flag:
        stable = 1
    else:
        stable = 2
    return stable

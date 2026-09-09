# The verifier should recover a correlation that a union analysis misses.
"""The verifier should recover a correlation that a union analysis misses."""


class A:
    def only_a(self):
        return True


class B:
    def only_b(self):
        return 5


def choose(flag):
    if flag:
        value = A()
    else:
        value = B()

    if flag:
        return value.only_a()
    return value.only_b()


RESULT = (choose(True), choose(False))

"""The result tag from one selected label drives the next dispatch site."""


class A:
    def next_value(self):
        return B()


class B:
    def only_b(self):
        return 5


value = A().next_value()
normal = value.only_b()

try:
    value.only_a()
except AttributeError as error:
    missing = type(error).__name__
else:
    missing = "not raised"

RESULT = (normal, missing)

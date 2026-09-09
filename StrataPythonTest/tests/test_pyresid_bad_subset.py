"""Deliberately outside the subset: exercises the accumulate-all checker.
Every construct below must appear in one rejection report."""
import os                            # import


class Meta(type):                    # metaclass definition is itself a class
    pass


class Sneaky(metaclass=Meta):        # metaclass-keyword
    count = 0                        # class-body-stmt

    def __getattr__(self, name):     # hook-override
        return 0

    def __radd__(self, other):       # reflected-dunder
        return self

    def __eq__(self, other):         # hash-eq-contract (no __hash__)
        return True


def outer():
    def inner():                     # nested-function
        return 1
    global count                     # global-stmt
    return inner()


def variadic(*args, **kwargs):       # starred-arg x2
    with open("f") as f:             # with-stmt
        del args                     # delete-stmt
    return lambda x: x               # lambda


squares = [x * y for x in range(3) for y in range(3)]  # multi-generator
pairs = {k: v for k, v in items}     # tuple comprehension target

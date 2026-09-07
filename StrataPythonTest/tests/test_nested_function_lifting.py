def helper(x: int) -> int:
    assert x == 99
    return x + 100


def left() -> int:
    def helper(x: int) -> int:
        assert x == 1
        return x + 1
    return helper(1)


def right() -> int:
    def helper(x: int) -> int:
        assert x == 2
        return x + 2
    return helper(2)


def shadow(outer: int) -> int:
    def helper(outer: int) -> int:
        return outer
    return helper(5)


def deep() -> int:
    def middle() -> int:
        def leaf(value: int) -> int:
            return value
        return leaf(7)
    return middle()


def recurse_once(flag: bool) -> int:
    def helper(again: bool) -> int:
        if again:
            return helper(False)
        return 11
    return helper(flag)


assert left() == 2
assert right() == 4
assert shadow(99) == 5
assert deep() == 7
assert recurse_once(True) == 11

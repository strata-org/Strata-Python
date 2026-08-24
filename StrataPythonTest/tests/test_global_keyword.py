counter: int = 0


def inc():
    global counter
    counter += 1


def set_nested_global():
    if True:
        global nested_value
    nested_value = 7


def local_shadow() -> int:
    counter: int = 40
    counter = counter + 2
    return counter


def test_globals():
    inc()
    inc()
    assert counter == 2, "global augmented assignment"

    set_nested_global()
    assert nested_value == 7, "nested declaration creates global"

    assert local_shadow() == 42, "assignment without global stays local"
    assert counter == 2, "local shadow preserves global"

test_globals()

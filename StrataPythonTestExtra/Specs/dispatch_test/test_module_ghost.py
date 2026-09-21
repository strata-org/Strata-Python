import servicelib.Ghost


def check_ghost_bound() -> bool:
    floor = servicelib.Ghost.floor_value()
    value = servicelib.Ghost.bounded_value()
    assert value >= floor, "value must be at least the ghost floor"
    return True

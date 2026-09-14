def delete_then_rebind() -> int:
    value = 1
    del value
    value = 2
    return value


def delete_then_read() -> int:
    value = 1
    del value
    return value

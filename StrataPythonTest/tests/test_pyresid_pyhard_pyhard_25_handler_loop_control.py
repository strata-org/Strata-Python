class LoopError(Exception):
    pass


def break_from_handler(values: list[int]) -> int:
    for item in values:
        try:
            raise LoopError()
        except LoopError as caught:
            result = item
            break
    else:
        result = 0 - 1
    return result


def continue_from_handler(values: list[int]) -> int:
    for item in values:
        try:
            raise LoopError()
        except LoopError as caught:
            last = item
            continue
    return last

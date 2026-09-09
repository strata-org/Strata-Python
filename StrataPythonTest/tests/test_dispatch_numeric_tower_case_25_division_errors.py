"""Division rows retain zero-divisor and integer/float conversion failures."""


def observe():
    try:
        1 / 0
    except BaseException as error:
        true_divide = type(error).__name__

    try:
        1.0 // 0.0
    except BaseException as error:
        floor_divide = type(error).__name__

    try:
        1 % 0
    except BaseException as error:
        modulo = type(error).__name__

    huge = 10**10000
    try:
        huge / 1.0
    except BaseException as error:
        conversion = type(error).__name__

    normal = 3 / 2
    return (
        true_divide,
        floor_divide,
        modulo,
        conversion,
        (type(normal).__name__, normal),
    )


RESULT = observe()

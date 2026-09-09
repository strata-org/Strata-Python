# Mixed int/float arithmetic may fail while float/float remains normal.
"""Mixed int/float arithmetic may fail while float/float remains normal."""


def observe():
    huge = 10**10000

    try:
        huge + 1.0
    except BaseException as error:
        addition = type(error).__name__

    try:
        1.0 - huge
    except BaseException as error:
        subtraction = type(error).__name__

    try:
        huge * 1.0
    except BaseException as error:
        multiplication = type(error).__name__

    normal = 1.5 + 2.5
    return (
        addition,
        subtraction,
        multiplication,
        (type(normal).__name__, normal),
    )


RESULT = observe()

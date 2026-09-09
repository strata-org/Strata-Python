"""Power can raise two numeric errors or leave the launch tag alphabet."""


def observe():
    try:
        0**-1
    except BaseException as error:
        zero_negative = type(error).__name__

    huge = 10**10000
    try:
        huge**-1
    except BaseException as error:
        conversion = type(error).__name__

    try:
        2.0**10000
    except BaseException as error:
        magnitude = type(error).__name__

    integral_negative_exponent = 2**-1
    float_complex = (-2.0) ** 0.5
    integer_complex = (-2) ** 0.5
    return (
        zero_negative,
        conversion,
        magnitude,
        (type(integral_negative_exponent).__name__, integral_negative_exponent),
        type(float_complex).__name__,
        type(integer_complex).__name__,
    )


RESULT = observe()

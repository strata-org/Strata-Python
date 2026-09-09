# Case 16 failure and walrus
class E(Exception):
    pass


x = "module x"


def body_failure():
    marker = -1
    try:
        result = [10 // (marker := x) for x in [2, 0, 5]]
    except ZeroDivisionError:
        try:
            result
        except UnboundLocalError:
            result_state = "UnboundLocalError"
        else:
            result_state = "bound"
    return marker, result_state, x


def filter_failure():
    marker = -2
    try:
        result = [
            item
            for item in [1, 2, 3]
            if 10 // (marker := item - 2)
        ]
    except ZeroDivisionError:
        try:
            result
        except UnboundLocalError:
            result_state = "UnboundLocalError"
        else:
            result_state = "bound"
    return marker, result_state


def exception_target_erases_walrus_binding():
    value = -1
    values = [item for item in [1, 2] if (value := item)]
    try:
        raise E("caught")
    except E as value:
        caught = str(value)

    try:
        value
    except UnboundLocalError:
        value_state = "UnboundLocalError"
    else:
        value_state = "bound"
    return values, caught, value_state


RESULT = (
    body_failure(),
    filter_failure(),
    exception_target_erases_walrus_binding(),
)

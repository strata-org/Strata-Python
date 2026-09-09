class E(Exception):
    pass


class Marker:
    value: int

    def __init__(self, value):
        self.value = value


def normal_completion():
    marker = Marker(0)
    try:
        marker.value = 0
    finally:
        marker.value = 1
    return marker.value


def return_completion():
    marker = Marker(0)
    try:
        return marker
    finally:
        marker.value = 1


def break_completion():
    marker = Marker(0)
    for _ in [0]:
        try:
            break
        finally:
            marker.value = 1
    return marker.value


def continue_completion():
    marker = Marker(0)
    for _ in [0]:
        try:
            continue
        finally:
            marker.value = 1
    return marker.value


def raise_completion():
    marker = Marker(0)
    try:
        try:
            raise E("pending")
        finally:
            marker.value = 1
    except E:
        return marker.value


RESULT = (
    normal_completion(),
    return_completion().value,
    break_completion(),
    continue_completion(),
    raise_completion(),
)

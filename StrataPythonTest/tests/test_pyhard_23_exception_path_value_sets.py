class Early:
    def marker(self) -> int:
        return 1


class Late:
    def marker(self) -> str:
        return "late"


class RouteError(Exception):
    pass


def split_at_handler(flag: bool) -> int | str:
    value = Early()
    try:
        if flag:
            raise RouteError()
        value = Late()
    except RouteError as route_error:
        return value.marker()
    else:
        return value.marker()


def join_after_handler(flag: bool) -> int | str:
    value = Early()
    try:
        if flag:
            raise RouteError()
        value = Late()
    except RouteError as route_error:
        selected = value
    else:
        selected = value
    return selected.marker()

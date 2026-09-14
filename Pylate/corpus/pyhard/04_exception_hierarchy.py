class LocalFileError(FileNotFoundError):
    pass


class HasOperation:
    def operation(self) -> int:
        return 7


class MissingOperation:
    pass


def caught_dispatch(value: HasOperation | MissingOperation) -> int:
    try:
        return value.operation()
    except AttributeError as attribute_error:
        return 0


def routed_exception(flag: bool) -> int:
    try:
        if flag:
            raise LocalFileError()
        raise KeyError()
    except OSError as os_error:
        return 1
    except LookupError as lookup_error:
        raise ValueError()

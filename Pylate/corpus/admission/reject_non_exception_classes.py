class Plain:
    pass


def invalid_raise():
    raise Plain()


def invalid_handler():
    try:
        raise ValueError()
    except Plain:
        return None


def unknown_raise():
    raise MissingError()


def unknown_handler():
    try:
        raise ValueError()
    except MissingError:
        return None

class E(Exception):
    pass


class ReplacementError(Exception):
    pass


def after_fallthrough():
    target = "before"
    try:
        raise E("caught")
    except E as target:
        pass
    try:
        return target
    except UnboundLocalError:
        return "UnboundLocalError"


def after_break():
    target = "before"
    for _ in [0]:
        try:
            raise E("caught")
        except E as target:
            break
    try:
        return target
    except UnboundLocalError:
        return "UnboundLocalError"


def after_continue():
    target = "before"
    for _ in [0]:
        try:
            raise E("caught")
        except E as target:
            continue
    try:
        return target
    except UnboundLocalError:
        return "UnboundLocalError"


def after_new_exception():
    target = "before"
    try:
        try:
            raise E("caught")
        except E as target:
            raise ReplacementError("replacement")
    except ReplacementError:
        pass
    try:
        return target
    except UnboundLocalError:
        return "UnboundLocalError"


def reader_returned_from_handler():
    target = "before"
    try:
        raise E("caught")
    except E as target:
        def read_target():
            return target

        return read_target


def after_explicit_delete():
    try:
        raise E("caught")
    except E as target:
        del target
    try:
        return target
    except UnboundLocalError:
        return "UnboundLocalError"


returned_reader = reader_returned_from_handler()
try:
    returned_reader()
except NameError:
    returned_reader_result = "NameError"
else:
    returned_reader_result = "still bound"

RESULT = (
    after_fallthrough(),
    after_break(),
    after_continue(),
    after_new_exception(),
    returned_reader_result,
    after_explicit_delete(),
)

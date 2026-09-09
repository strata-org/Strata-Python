class ShortIterator:
    position: int

    def __init__(self):
        self.position = 0

    def __iter__(self):
        return self

    def __next__(self):
        self.position += 1
        if self.position == 2:
            raise StopIteration("iterator exhausted")
        return self.position


class FailingIterator:
    def __iter__(self):
        return self

    def __next__(self):
        raise ValueError("iterator failed")


class IteratorSetupFails:
    def __iter__(self):
        raise LookupError("iterator setup failed")


class InvalidIterator:
    def __iter__(self):
        return 1


def stop_iteration_from_body_propagates():
    try:
        for _ in [0]:
            raise StopIteration("from body")
    except StopIteration:
        return "StopIteration"


def exhaustion_runs_loop_else():
    for _ in ShortIterator():
        pass
    else:
        return "else"


def other_iterator_error_skips_loop_else():
    try:
        for _ in FailingIterator():
            pass
        else:
            return "else"
    except ValueError:
        return "ValueError"


def iterator_setup_error_propagates():
    try:
        for _ in IteratorSetupFails():
            pass
    except LookupError:
        return "LookupError"


def invalid_iterator_result_is_type_error():
    try:
        for _ in InvalidIterator():
            pass
    except TypeError:
        return "TypeError"


RESULT = (
    list(ShortIterator()),
    stop_iteration_from_body_propagates(),
    exhaustion_runs_loop_else(),
    other_iterator_error_skips_loop_else(),
    iterator_setup_error_propagates(),
    invalid_iterator_result_is_type_error(),
)

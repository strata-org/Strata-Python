class BoolError(Exception):
    pass


class BoolRaises:
    def __bool__(self):
        raise BoolError("bool failed")


class LengthRaises:
    def __len__(self):
        raise LookupError("length failed")


class NegativeLength:
    def __len__(self):
        return -1


class NonIntegerLength:
    def __len__(self):
        return "one"


class BoolPrecedesLength:
    def __bool__(self):
        return False

    def __len__(self):
        raise LookupError("must not run")


def observe_truth_testing():
    try:
        if BoolRaises():
            pass
    except BoolError:
        bool_result = "BoolError"

    try:
        if LengthRaises():
            pass
    except LookupError:
        length_result = "LookupError"

    try:
        bool(NegativeLength())
    except ValueError:
        negative_result = "ValueError"

    try:
        bool(NonIntegerLength())
    except TypeError:
        non_integer_result = "TypeError"

    precedence_result = bool(BoolPrecedesLength())
    return (
        bool_result,
        length_result,
        negative_result,
        non_integer_result,
        precedence_result,
    )


RESULT = observe_truth_testing()

class Empty:
    pass


def observe_errors():
    try:
        {}["missing"]
    except KeyError:
        dict_result = "KeyError"

    try:
        [1][2]
    except IndexError:
        index_result = "IndexError"

    try:
        [1][::0]
    except ValueError:
        slice_result = "ValueError"

    try:
        1 // 0
    except ZeroDivisionError:
        division_result = "ZeroDivisionError"

    try:
        1 + "x"
    except TypeError:
        addition_result = "TypeError"

    try:
        left, right = [1]
    except ValueError:
        unpack_result = "ValueError"

    try:
        Empty().missing
    except AttributeError:
        attribute_result = "AttributeError"

    try:
        assert False, "failed"
    except AssertionError:
        assertion_result = "AssertionError"

    return (
        dict_result,
        index_result,
        slice_result,
        division_result,
        addition_result,
        unpack_result,
        attribute_result,
        assertion_result,
    )


RESULT = observe_errors()

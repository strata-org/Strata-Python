def source_precedes_body():
    try:
        [1 // 0 for item in [][1]]
    except IndexError:
        return "IndexError"
    except ZeroDivisionError:
        return "ZeroDivisionError"


def filter_precedes_body():
    try:
        [[1][2] for item in [1] if 1 // 0]
    except ZeroDivisionError:
        return "ZeroDivisionError"
    except IndexError:
        return "IndexError"


def dict_key_precedes_value():
    try:
        {1 // 0: [1][2] for item in [1]}
    except ZeroDivisionError:
        return "ZeroDivisionError"
    except IndexError:
        return "IndexError"


RESULT = (
    source_precedes_body(),
    filter_precedes_body(),
    dict_key_precedes_value(),
)

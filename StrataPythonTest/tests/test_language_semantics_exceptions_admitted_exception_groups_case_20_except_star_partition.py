# Case 20 except star partition
def partition_group():
    values = ()
    types = ()
    try:
        raise ExceptionGroup(
            "source",
            [ValueError("a"), TypeError("b"), ValueError("c")],
        )
    except* ValueError as group:
        values = tuple([str(item) for item in group.exceptions])
    except* TypeError as group:
        types = tuple([str(item) for item in group.exceptions])

    try:
        group
    except UnboundLocalError:
        target_state = "UnboundLocalError"
    else:
        target_state = "bound"
    return values, types, target_state


RESULT = partition_group()

class E(Exception):
    pass


def continue_from_handler():
    handled = 0
    loop_else = "skipped"
    for _ in [0, 1]:
        try:
            raise E("caught")
        except E as error:
            handled += 1
            continue
    else:
        loop_else = "else"

    try:
        error
    except UnboundLocalError:
        target_state = "UnboundLocalError"
    else:
        target_state = "still bound"
    return handled, loop_else, target_state


def break_from_handler():
    handled = 0
    loop_else = "skipped"
    for _ in [0, 1]:
        try:
            raise E("caught")
        except E as error:
            handled += 1
            break
    else:
        loop_else = "else"

    try:
        error
    except UnboundLocalError:
        target_state = "UnboundLocalError"
    else:
        target_state = "still bound"
    return handled, loop_else, target_state


RESULT = continue_from_handler(), break_from_handler()

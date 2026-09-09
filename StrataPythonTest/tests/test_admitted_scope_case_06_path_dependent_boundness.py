class E(Exception):
    pass


def success_path():
    try:
        x = 10
        y = 20
    except E as error:
        z = 30
    else:
        w = 40
    finally:
        try:
            x_result = x
        except UnboundLocalError:
            x_result = "UnboundLocalError"
        try:
            y_result = y
        except UnboundLocalError:
            y_result = "UnboundLocalError"
        try:
            z_result = z
        except UnboundLocalError:
            z_result = "UnboundLocalError"
        try:
            w_result = w
        except UnboundLocalError:
            w_result = "UnboundLocalError"
        try:
            error_result = error
        except UnboundLocalError:
            error_result = "UnboundLocalError"
    return x_result, y_result, z_result, w_result, error_result


def exceptional_path():
    try:
        x = 10
        raise E("stop")
        y = 20
    except E as error:
        z = 30
    else:
        w = 40
    finally:
        try:
            x_result = x
        except UnboundLocalError:
            x_result = "UnboundLocalError"
        try:
            y_result = y
        except UnboundLocalError:
            y_result = "UnboundLocalError"
        try:
            z_result = z
        except UnboundLocalError:
            z_result = "UnboundLocalError"
        try:
            w_result = w
        except UnboundLocalError:
            w_result = "UnboundLocalError"
        try:
            error_result = error
        except UnboundLocalError:
            error_result = "UnboundLocalError"
    return x_result, y_result, z_result, w_result, error_result


RESULT = success_path(), exceptional_path()

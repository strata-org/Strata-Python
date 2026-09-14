# Interaction: the five flow modes crossing finally: return in try with
# finally effects, break inside try inside a loop, a user raise passing
# through finally uncaught by the inner handler.
class Oops(Exception):
    pass


def modes(k: int) -> int:
    log = []
    for i in range(k):
        try:
            if i == 0:
                break
            log.append(1)
        finally:
            log.append(2)
    try:
        if k > 0:
            raise Oops()
        return len(log)
    except ValueError:
        return -1
    finally:
        log.append(3)


r = modes(1)

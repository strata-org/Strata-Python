# `close()` injects GeneratorExit so the body's `finally` runs, then swallows
# the exit. What the cleanup raises must escape: CPython raises ValueError from
# close_noisy and returns None from close_quiet.
def cleanup_raises(n: int):
    try:
        yield n
    finally:
        raise ValueError("cleanup failed")


def quiet(n: int):
    try:
        yield n
    finally:
        pass


def close_noisy(n: int) -> None:
    g = cleanup_raises(n)
    v = next(g)
    g.close()


def close_quiet(n: int) -> None:
    g = quiet(n)
    v = next(g)
    g.close()

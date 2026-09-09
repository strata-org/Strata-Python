"""A conditional return in finally still discards the pending exception."""


def cleanup():
    return "cleanup result"


def run(should_return):
    try:
        raise StopIteration("pending")
    finally:
        if should_return:
            return cleanup()


RESULT = run(True)


if __name__ == "__main__":
    print(repr(RESULT))

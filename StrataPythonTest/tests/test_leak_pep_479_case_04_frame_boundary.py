"""Case 4 (PEP 479): Conversion occurs at resumable frame boundaries."""

import asyncio


def generator():
    if False:
        yield None
    raise StopIteration("from generator")


async def coroutine():
    raise StopIteration("from coroutine")


def plain_function():
    raise StopIteration("from plain function")


def describe(thunk):
    try:
        thunk()
    except BaseException as error:
        cause = type(error.__cause__).__name__ if error.__cause__ else None
        context = type(error.__context__).__name__ if error.__context__ else None
        return type(error).__name__, cause, context, error.__suppress_context__
    return "no exception", None, None, False


RESULT = {
    "generator": describe(lambda: list(generator())),
    "coroutine": describe(lambda: asyncio.run(coroutine())),
    "plain": describe(plain_function),
}


if __name__ == "__main__":
    print(repr(RESULT))

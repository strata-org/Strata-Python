"""An async-generator StopAsyncIteration is converted to RuntimeError."""

import asyncio


async def generator():
    yield 1
    raise StopAsyncIteration("from async generator")


async def consume():
    values = []
    try:
        async for value in generator():
            values.append(value)
    except RuntimeError as error:
        return values, type(error).__name__, type(error.__cause__).__name__
    return values, "no exception", None


RESULT = asyncio.run(consume())


if __name__ == "__main__":
    print(repr(RESULT))

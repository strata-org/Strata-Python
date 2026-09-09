"""StopAsyncIteration from a helper silently truncates async iteration."""

import asyncio


def transform(value):
    if value == 2:
        raise StopAsyncIteration("async transform failed")
    return value


class AsyncItems:
    def __init__(self):
        self.index = 0

    def __aiter__(self):
        return self

    async def __anext__(self):
        self.index += 1
        return transform(self.index)


async def collect():
    values = []
    async for value in AsyncItems():
        values.append(value)
    return values


RESULT = asyncio.run(collect())


if __name__ == "__main__":
    print(repr(RESULT))

# Async functions are function scopes like any other.
async def f(xs):
    async with lock as l:
        async for x in xs:
            await g(x, l)

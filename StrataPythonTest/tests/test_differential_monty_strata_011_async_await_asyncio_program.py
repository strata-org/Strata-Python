# Feature: async def / await / asyncio (coroutines).
#
# Monty (pydantic-monty 0.0.18): IN. `async def`/`await` work; coroutines call each
#   other; asyncio.run(coro) and asyncio.gather(*aws) are the only asyncio functions
#   (limitations/asyncio.md). No in-sandbox event loop — the host is the loop.
#   Coroutines are single-shot; `async for`/`async with`/async comprehensions are
#   REJECTED AT PARSE TIME (same as CPython would allow, so Monty is stricter there).
#
# Strata front end: REJECTS. `AsyncFunctionDef` and `Await` are not handled cases in
#   translateStmt/translateExpr; they hit the catch-all `unsupportedConstruct`
#   (PythonToLaurel.lean:2119 / expr catch-all). Pending: test_async_def.py,
#   test_await.py. No `test_soundness_async_*` => rejected, not mis-modeled. Safe.
#
# Frontend verdict: OUT. frontend-subset.md: "Generators and coroutines: yield, yield from,
#   async def, await" OUT ("frame-suspension semantics require a state-machine encoding
#   Laurel does not have today"); `asyncio` OUT under Libraries ("concurrency out of
#   scope; the soundness story is single-threaded with the GIL"). Rejected => cell (C).

import asyncio


async def double(x: int) -> int:
    return x * 2


async def add(a: int, b: int) -> int:
    da: int = await double(a)
    db: int = await double(b)
    return da + db


async def main_coro() -> list:
    r: int = await add(3, 4)                              # (3*2)+(4*2) = 14
    pair: list = await asyncio.gather(double(5), double(6))  # [10, 12]
    return [r, pair[0], pair[1]]


asyncio.run(main_coro())

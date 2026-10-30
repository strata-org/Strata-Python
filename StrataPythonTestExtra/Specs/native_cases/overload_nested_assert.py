from typing import overload

# An @overload stub's body is not read, so an assert in it is rejected at any depth. Each
# stub nests one assert in another kind of block; no_assert nests none.
@overload
def in_while(x: int) -> int:
    while x > 0:
        assert x > 1

@overload
def in_while_else(x: int) -> int:
    while x > 0:
        pass
    else:
        assert x > 1

@overload
def in_with(x: int) -> int:
    with x:
        assert x > 1

@overload
def in_try(x: int) -> int:
    try:
        assert x > 1
    except ValueError:
        pass

@overload
def in_handler(x: int) -> int:
    try:
        pass
    except ValueError:
        assert x > 1

@overload
def in_try_else(x: int) -> int:
    try:
        pass
    except ValueError:
        pass
    else:
        assert x > 1

@overload
def in_finally(x: int) -> int:
    try:
        pass
    finally:
        assert x > 1

@overload
def in_try_star(x: int) -> int:
    try:
        pass
    except* ValueError:
        assert x > 1

@overload
def in_match(x: int) -> int:
    match x:
        case 1:
            assert x > 1

@overload
def in_def(x: int) -> int:
    def g() -> None:
        assert x > 1

@overload
def in_class(x: int) -> int:
    class K:
        assert x > 1

@overload
def in_async_for(x: int) -> int:
    async for y in x:
        assert x > 1

@overload
def in_async_with(x: int) -> int:
    async with x:
        assert x > 1

@overload
def in_async_def(x: int) -> int:
    async def g() -> None:
        assert x > 1

@overload
def no_assert(x: int) -> int:
    while x > 0:
        pass
    try:
        pass
    finally:
        pass

class P:
    @overload
    def m(self, x: int) -> int:
        while x > 0:
            try:
                pass
            except ValueError:
                assert x > 1

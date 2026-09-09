"""Case 9 (observability): Tracebacks cannot reveal exhaustion intent."""

import dis


def raise_site(error):
    traceback = error.__traceback__.tb_next
    if traceback is None:
        return None

    depth = 0
    last = traceback
    while last.tb_next is not None:
        last = last.tb_next
        depth += 1

    instruction = next(
        item.opname
        for item in dis.get_instructions(last.tb_frame.f_code)
        if item.offset == last.tb_lasti
    )
    return last.tb_frame.f_code.co_qualname, instruction, depth


class Propagating:
    def __init__(self, source):
        self.iterator = iter(source)

    def __iter__(self):
        return self

    def __next__(self):
        return next(self.iterator)


class Explicit:
    END = object()

    def __init__(self, source):
        self.iterator = iter(source)

    def __iter__(self):
        return self

    def __next__(self):
        value = next(self.iterator, self.END)
        if value is self.END:
            raise StopIteration
        return value


def observe(iterator):
    try:
        next(iterator)
    except StopIteration as error:
        return raise_site(error)
    return "no exception"


RESULT = {
    "builtin": observe(iter([])),
    "propagating": observe(iter(Propagating([]))),
    "explicit": observe(iter(Explicit([]))),
}


if __name__ == "__main__":
    print(repr(RESULT))

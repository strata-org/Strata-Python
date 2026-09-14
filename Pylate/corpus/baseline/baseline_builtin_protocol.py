class LengthBomb:
    def __len__(self) -> int:
        raise LookupError()


class IterBomb:
    def __iter__(self):
        raise RuntimeError()


class NextBomb:
    def __next__(self):
        raise ValueError()


def length() -> str:
    try:
        result = len(LengthBomb())
        return "missed-len-error"
    except LookupError:
        return "caught-len-error"


def iteration() -> str:
    try:
        result = iter(IterBomb())
        return "missed-iter-error"
    except RuntimeError:
        return "caught-iter-error"


def next_item() -> str:
    try:
        result = next(NextBomb())
        return "missed-next-error"
    except ValueError:
        return "caught-next-error"


length_result = length()
iter_result = iteration()
next_result = next_item()

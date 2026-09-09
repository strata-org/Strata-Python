class StrBomb:
    def __str__(self) -> str:
        raise LookupError()


class ReprBomb:
    def __repr__(self) -> str:
        raise RuntimeError()


class ReprOnlyBomb:
    def __repr__(self) -> str:
        raise OSError()


class BadStrResult:
    def __str__(self) -> int:
        return 1


def stringify() -> str:
    try:
        return str(StrBomb())
    except LookupError:
        return "caught-str-error"


def represent() -> str:
    try:
        return repr(ReprBomb())
    except RuntimeError:
        return "caught-repr-error"


def default_string_uses_repr() -> str:
    try:
        return str(ReprOnlyBomb())
    except OSError:
        return "caught-default-repr-error"


def bad_string_result() -> str:
    try:
        return str(BadStrResult())
    except TypeError:
        return "caught-bad-str-result"


str_result = stringify()
repr_result = represent()
default_result = default_string_uses_repr()
bad_result = bad_string_result()

class ReflectedAdd:
    def __radd__(self, other) -> int:
        return 7


class DeclinedAdd:
    def __radd__(self, other):
        return NotImplemented


class ModTrap:
    def __rmod__(self, other) -> str:
        return "must not run"


class StrRaises:
    def __str__(self) -> str:
        raise RuntimeError()


class ReprRaises:
    def __repr__(self) -> str:
        raise LookupError()


class MappingRaises:
    def __getitem__(self, key: str) -> str:
        raise OSError()


class ConvertedStrRaises:
    def __str__(self) -> str:
        raise RuntimeError()


class MappingReturnsRaisingValue:
    def __getitem__(self, key: str) -> ConvertedStrRaises:
        return ConvertedStrRaises()


class IntPreferred:
    def __int__(self) -> int:
        return 3

    def __index__(self) -> int:
        raise LookupError()


class AlternativeFormat:
    def __getitem__(self, key: str) -> int:
        return 3

    def __str__(self) -> str:
        raise RuntimeError()


class Negates:
    def __neg__(self) -> str:
        return "negative"


class NegRaises:
    def __neg__(self) -> int:
        raise ArithmeticError()


class Indexed:
    def __index__(self) -> int:
        return 2


class ForwardWins:
    def __add__(self, other) -> int:
        return 1


class ReflectedLoses:
    def __radd__(self, other) -> str:
        return "wrong"


class ForwardRaises:
    def __add__(self, other):
        raise LookupError()


class ReflectedUnreachable:
    def __radd__(self, other) -> int:
        return 99


class SameType:
    def __add__(self, other):
        return NotImplemented

    def __radd__(self, other) -> int:
        return 5


class ReflectedOps:
    def __rsub__(self, other) -> int:
        return 1

    def __rmul__(self, other) -> int:
        return 2

    def __rtruediv__(self, other) -> int:
        return 3

    def __rfloordiv__(self, other) -> int:
        return 4

    def __rmod__(self, other) -> int:
        return 5

    def __rpow__(self, other) -> int:
        return 6

    def __rlshift__(self, other) -> int:
        return 7

    def __rrshift__(self, other) -> int:
        return 8

    def __rand__(self, other) -> int:
        return 9

    def __rxor__(self, other) -> int:
        return 10

    def __ror__(self, other) -> int:
        return 11


class ViewReflectedTrap:
    def __rand__(self, other) -> int:
        return 12


class TypeA:
    pass


class TypeB:
    pass


numeric_reflected = 1 + ReflectedAdd()
sequence_reflected = [1] + ReflectedAdd()


def sequence_declined_case():
    return [1] + DeclinedAdd()


reflected_subtract = 1 - ReflectedOps()
reflected_multiply = 1 * ReflectedOps()
reflected_divide = 1 / ReflectedOps()
reflected_floor_divide = 1 // ReflectedOps()
reflected_modulo = 1 % ReflectedOps()
reflected_power = 1 ** ReflectedOps()
reflected_left_shift = 1 << ReflectedOps()
reflected_right_shift = 1 >> ReflectedOps()
reflected_and = 1 & ReflectedOps()
reflected_xor = 1 ^ ReflectedOps()
reflected_or = 1 | ReflectedOps()


def plain_format_error_case():
    return "ab" % 3


plain_format_mapping = "ab" % []
string_format = "%s" % 3


def numeric_format_error_case():
    return "%d" % "x"


def format_blocks_reflected_case():
    return "plain" % ModTrap()


def string_hook_raises_case():
    return "%s" % StrRaises()


def repr_hook_raises_case():
    return "%r" % ReprRaises()


def mapping_hook_raises_case():
    return "%(key)s" % MappingRaises()


def mapping_value_hook_raises_case():
    return "%(key)s" % MappingReturnsRaisingValue()


ordered_decimal_hook = "%d" % IntPreferred()
user_negation = -Negates()


def user_negation_raises_case():
    return -NegRaises()

forward_wins = ForwardWins() + ReflectedLoses()


def forward_raise_stops_case():
    return ForwardRaises() + ReflectedUnreachable()


def same_type_skips_reflected_case():
    return SameType() + SameType()

tuple_concat = (1,) + ("x",)
tuple_repeat_right = (1,) * 2
tuple_repeat_left = 2 * (1,)
list_repeat_may_overflow = [1] * 2
string_index_repeat = "x" * Indexed()
list_index_repeat = Indexed() * [1]
left_shift_may_overflow = 1 << 2

set_subtract = {1, 2} - {2}
set_intersection = {1, 2} & {2}
set_symmetric_difference = {1, 2} ^ {2, 3}
set_union = {1, 2} | {2, 3}
dict_union = {"a": 1} | {"b": "x"}

keys = {"a": 1}.keys()
items = {"a": 1}.items()
values = {"a": 1}.values()
keys_intersection = keys & ["a"]
items_union = items | {("b", 2)}


def values_union_case():
    values = {"a": 1}.values()
    return values | {1}


def keys_block_reflected_case():
    keys = {"a": 1}.keys()
    return keys & ViewReflectedTrap()


values_reach_reflected = values & ViewReflectedTrap()
set_reaches_reflected = {1} | ReflectedOps()
dict_reaches_reflected = {"a": 1} | ReflectedOps()
same_runtime_type = TypeA | TypeA
different_runtime_types = TypeA | TypeB
optional_runtime_type = TypeA | None
chained_runtime_type = (TypeA | TypeB) | None


def power_results(left: float, right: float):
    return left ** right


def runtime_numeric_narrowing(value: bool | int | float | complex):
    if isinstance(value, int):
        return value + 1
    if isinstance(value, complex):
        return -value
    return value


def decimal_format_float(value: float):
    return "%d" % value


def joined_format_literals(flag: bool):
    fmt = "%s" if flag else "plain"
    return fmt % AlternativeFormat()

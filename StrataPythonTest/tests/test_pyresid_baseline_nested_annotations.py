def list_head(values: list[int]) -> int:
    return values[0]


def dict_value(values: dict[str, int]) -> int:
    return values["key"]


def tuple_second(values: tuple[int, str]) -> str:
    return values[1]


def accept_set(values: set[int]) -> None:
    return None


def bad_list_case():
    return list_head(["not-an-int"])


def bad_dict_case():
    return dict_value({"key": "not-an-int"})


def bad_tuple_case():
    return tuple_second((1, 2))


def bad_set_case():
    return accept_set({"not-an-int"})

from typing import NotRequired, Required, TypedDict


class InventoryRow(TypedDict, total=False):
    name: Required[str]
    count: int
    note: NotRequired[str]


def builtin_functions() -> None:
    values = [1, 2, 3]
    size = len(values)
    text = str(size)
    shown = repr(values)
    print(text, shown, sep=":", end="\n", flush=False)
    is_list = isinstance(values, list)
    numbers = range(0, 4, 1)
    iterator = iter(values)
    first = next(iterator, 0)
    copied_list = list(numbers)
    copied_tuple = tuple(values)
    copied_set = set(values)
    copied_dict = dict({"size": size})


def list_methods() -> None:
    values = [3, 1, 2]
    appended = values.append(4)
    inserted = values.insert(0, 0)
    extended = values.extend([5, 6])
    popped = values.pop()
    removed = values.remove(0)
    counted = values.count(2)
    indexed = values.index(2)
    sorted_result = values.sort(reverse=False)
    reversed_result = values.reverse()
    copied = values.copy()
    cleared = values.clear()


def set_methods() -> None:
    values = {1, 2, 3}
    other = {2, 3, 4}
    added = values.add(5)
    discarded = values.discard(99)
    removed = values.remove(1)
    popped = values.pop()
    copied = values.copy()
    unioned = values.union(other, {6})
    intersected = values.intersection(other, {3, 4})
    differenced = values.difference(other, {8})
    symmetric = values.symmetric_difference(other)
    subset = values.issubset(other)
    superset = values.issuperset(other)
    disjoint = values.isdisjoint({20})
    updated = values.update(other, {7})

    difference_target = {1, 2, 3}
    difference_updated = difference_target.difference_update({2}, {8})
    intersection_target = {1, 2, 3}
    intersection_updated = intersection_target.intersection_update({2, 3})
    symmetric_target = {1, 2}
    symmetric_updated = symmetric_target.symmetric_difference_update({2, 3})

    cleared = values.clear()


def tuple_and_range_methods() -> None:
    pair = (1, 2, 1)
    tuple_count = pair.count(1)
    tuple_index = pair.index(2)
    numbers = range(0, 5)
    range_count = numbers.count(2)
    range_index = numbers.index(3)


def string_methods() -> None:
    value = " Alpha,beta "
    upper = value.upper()
    lower = value.lower()
    stripped = value.strip()
    left_stripped = value.lstrip()
    right_stripped = value.rstrip()
    titled = value.title()
    capitalized = value.capitalize()
    folded = value.casefold()
    swapped = value.swapcase()
    replaced = value.replace("a", "A", 1)
    joined = ",".join(["a", "b"])
    formatted = "{}:{}".format("a", 1)
    prefix_removed = value.removeprefix(" ")
    suffix_removed = value.removesuffix(" ")
    left_justified = value.ljust(20, ".")
    right_justified = value.rjust(20, ".")
    centered = value.center(20, ".")
    zero_filled = "12".zfill(4)
    tabs_expanded = "a\tb".expandtabs(4)
    starts = value.startswith(" ", 0, 2)
    ends = value.endswith(" ", 0, len(value))
    alnum = "abc1".isalnum()
    alpha = "abc".isalpha()
    ascii_only = value.isascii()
    decimal = "12".isdecimal()
    digit = "12".isdigit()
    identifier = "name".isidentifier()
    lower_case = "abc".islower()
    numeric = "12".isnumeric()
    printable = value.isprintable()
    whitespace = " \t".isspace()
    title_case = "A Title".istitle()
    upper_case = "ABC".isupper()
    counted = value.count("a", 0, len(value))
    found = value.find("a", 0, len(value))
    right_found = value.rfind("a", 0, len(value))
    indexed = value.index("A", 0, len(value))
    right_indexed = value.rindex("a", 0, len(value))
    split = value.split(",", 1)
    right_split = value.rsplit(",", 1)
    lines = "a\nb".splitlines(True)

    encoded = value.encode("utf-8", "strict")
    mapped_format = "{name}".format_map({"name": "value"})
    translation = value.maketrans("ab", "AB", " ")
    partitioned = value.partition(",")
    right_partitioned = value.rpartition(",")
    translated = value.translate(translation)


def dict_methods() -> None:
    values = {"a": 1, "b": 2}
    got = values.get("a", 0)
    popped = values.pop("b", 0)
    keys = values.keys()
    vals = values.values()
    items = values.items()
    defaulted = values.setdefault("c", 3)
    updated = values.update({"d": 4}, e=5)
    copied = values.copy()
    created = values.fromkeys(["x", "y"], 0)
    popped_item = values.popitem()
    cleared = values.clear()


def typed_dict_operations(row: InventoryRow) -> str:
    required_read = row["name"]
    row["name"] = required_read.upper()

    optional_value = row.get("count", 0)
    row.setdefault("count", optional_value)
    row.update(count=optional_value + 1)
    optional_read = row["count"]
    optional_present = "note" in row
    note = row.get("note", "")
    row["note"] = note
    removed_note = row.pop("note", "")

    keys = row.keys()
    values = row.values()
    items = row.items()
    copied = row.copy()
    return row["name"]


def exercise_typed_dict() -> str:
    row: InventoryRow = {"name": "widget"}
    return typed_dict_operations(row)


builtin_functions()
list_methods()
set_methods()
tuple_and_range_methods()
string_methods()
dict_methods()
typed_result = exercise_typed_dict()

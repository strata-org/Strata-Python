import servicelib.Storage


def check_delete(s: servicelib.Storage.Storage) -> None:
    s.delete_item("b", "k")

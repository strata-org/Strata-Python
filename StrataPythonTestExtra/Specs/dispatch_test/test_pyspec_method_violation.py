from servicelib.Storage import Storage


def check_get_violation(s: Storage) -> None:
    s.get_item(Bucket="", Key="k")

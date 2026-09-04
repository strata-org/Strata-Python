from servicelib.Storage import Storage


def check_get(s: Storage) -> None:
    s.get_item(Bucket="b", Key="k")

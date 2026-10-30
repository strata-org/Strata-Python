import servicelib.NotLocal


def call_with_none() -> bool:
    servicelib.NotLocal.check_if_local(None, 0)
    return True

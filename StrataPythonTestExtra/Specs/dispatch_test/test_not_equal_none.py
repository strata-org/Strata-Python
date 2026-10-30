import servicelib.NotLocal


def call_with_none() -> bool:
    servicelib.NotLocal.check_region(None)
    return True

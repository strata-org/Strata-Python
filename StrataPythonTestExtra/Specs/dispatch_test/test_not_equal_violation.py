import servicelib.NotLocal


def call_with_local() -> bool:
    servicelib.NotLocal.check_region("local")
    return True

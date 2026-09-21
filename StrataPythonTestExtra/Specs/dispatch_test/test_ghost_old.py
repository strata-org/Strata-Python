import servicelib.GhostOld


def check_counter_increments() -> bool:
    before = servicelib.GhostOld.alloc_count()
    servicelib.GhostOld.acquire("db")
    after = servicelib.GhostOld.alloc_count()
    assert after == before + 1, "acquire increments the ghost counter"
    return True


def check_resource_registered() -> bool:
    servicelib.GhostOld.acquire("db")
    assert servicelib.GhostOld.exists("db"), "acquired resource is registered"
    return True

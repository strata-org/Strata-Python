import servicelib.GhostProbe


def check_acquire_registers() -> bool:
    servicelib.GhostProbe.acquire("db")
    present = servicelib.GhostProbe.exists("db")
    assert present, "acquired resource is registered in the ghost table"
    return True

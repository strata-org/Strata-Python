import servicelib.GhostOldNoFrame


def check_never_verified() -> bool:
    servicelib.GhostOldNoFrame.bump()
    assert 1 == 2, "unframed ghost OLD must not verify anything"
    return True

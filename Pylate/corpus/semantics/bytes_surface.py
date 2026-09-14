# The bytes surface reachable from admitted code. Bytes literals are rejected by
# the subset, so a method taking a bytes argument cannot be called from an
# admitted program; these four go through `str.encode` and are the ones a real
# program can reach. Checked against CPython.
def probe(s: str) -> int:
    raw = s.encode()
    total = 0
    if raw.isalpha():
        total = total + 1
    return total


def to_hex(s: str) -> str:
    return s.encode().hex()


def round_trip(s: str) -> str:
    return s.encode().decode()


def padded(s: str) -> int:
    return len(s.encode().zfill(8))

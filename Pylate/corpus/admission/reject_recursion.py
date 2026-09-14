"""Recursion is outside the admitted subset.

Summarising a call whose body is already on the stack needs a contract stating
the callee's result, the exceptions it may raise, the locations it may write and
the values written there -- checked, not assumed. Absent that, the only sound
summary is "returns anything, raises anything, havocs everything reachable".

The analyser previously assumed the declared return annotation, no raise, and no
write. All three are false in general; `../../doc/RECURSION_CONTRACTS.md` records
the measurements. Rejecting is the honest interim.

`count` is direct recursion; `ping`/`pong` are mutual.
"""


def count(n: int) -> int:
    if n:
        return count(n - 1) + 1
    return 0


def ping(n: int) -> int:
    return pong(n)


def pong(n: int) -> int:
    return ping(n)

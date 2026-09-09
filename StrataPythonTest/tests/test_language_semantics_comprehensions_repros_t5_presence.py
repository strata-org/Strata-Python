# Does the frontend model TypedDict key PRESENCE for required vs. NotRequired?
#
# Avoids len() entirely, because a stub's container length is unconstrained and
# can be negative (t3/t4), which would mask the result.
#
# In Python: reading a NotRequired key that is absent raises KeyError. So the
# read of c['retries'] below carries an obligation; the read of c['name'] does not.
from typing import TypedDict, NotRequired


class Cfg(TypedDict):
    name: str
    retries: NotRequired[int]


def get_cfg() -> Cfg:
    return {"name": "worker", "retries": 3}


def main() -> None:
    c = get_cfg()
    r = c['retries']      # OPTIONAL key, unguarded -> expect a KeyError property
    assert r == r         # trivially true; we only care about the property LIST


main()

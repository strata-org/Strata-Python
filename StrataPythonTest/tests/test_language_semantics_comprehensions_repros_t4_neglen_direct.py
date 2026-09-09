# Control for t3: a DIRECTLY stub-returned list, no TypedDict field read.
# Isolates whether the missing length>=0 constraint comes from the stub return
# or from the dict field read.
from typing import List


def get_names() -> List[str]:
    return ["alpha", "beta"]


def main() -> None:
    ns = get_names()
    assert len(ns) >= 0, "len() is never negative"


main()

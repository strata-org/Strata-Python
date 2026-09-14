# Badly behaved, inside the fragment: a variable bound on only one
# branch and read after the join (maybe-unbound obligation), and a
# store to a frozen dataclass outside __init__ (guaranteed abort
# FrozenInstanceError under strict).
from dataclasses import dataclass


@dataclass(frozen=True)
class Tag:
    name: str


def label(flag: bool) -> str:
    if flag:
        text = "on"
    return text


t = Tag("alpha")
t.name = "beta"
lbl = label(True)

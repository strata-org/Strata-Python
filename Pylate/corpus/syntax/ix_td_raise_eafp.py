# TypedDict undeclared-key read under the eafp preset (from the _eafp
# suffix): the guaranteed KeyError row stays a MODELED raise (key is
# relaxed), so the dispatch table shows target kind "raise" and the
# module may raise KeyError; under strict this same row would be abort.
from typing import TypedDict


class Movie(TypedDict):
    title: str


m = Movie(title="Alien")
bad = m["year"]

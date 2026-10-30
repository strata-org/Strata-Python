# Declared shapes of TypedDicts: the bases and keywords, and each key's annotation as
# written, with Required, NotRequired and ReadOnly left in, for Pylate to read.
import typing
from typing import Callable, Literal, NotRequired, Required
from typing import TypedDict as TD
from typing_extensions import ReadOnly


class Movie(TD):
    title: str
    year: int | None
    tags: typing.List[str]
    rating: Literal[1, -2, "three", None]
    sequel: "Movie"
    pick: Callable[[int], str]


class Draft(TD, total=False):
    title: Required[str]
    notes: str
    owner: ReadOnly[NotRequired[str]]


class Sequel(Movie):
    prequel: Movie

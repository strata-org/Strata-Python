from typing import NotRequired, TypedDict


class Movie(TypedDict):
    title: str
    year: int
    rating: NotRequired[int]


def revise(movie: Movie, year: int) -> str:
    movie["year"] = year
    movie.update(rating=5)
    movie.setdefault("rating", 0)
    current = movie.get("rating")
    if current is None:
        return movie["title"]
    return movie["title"]

# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
from typing import NotRequired, TypedDict


class Movie(TypedDict):
    title: str
    year: int
    rating: NotRequired[int]


# L10 pyhard[summary revise] returns={str}; escapes={}
# L10 pyhard[type parameter] assert/assume conforms(movie, Movie); boundary nondet over 17 closed tags
# L10 pyhard[type parameter] assert/assume conforms(year, int); boundary nondet over 17 closed tags
# L10 pyhard[shape typed_dict_parameter] assert/assume shape_Movie(movie)
def revise(movie: Movie, year: int) -> str:
    # L11 pyhard[flow revise in] current -> (binding=definitely_unbound; tags={}; defs={unbound:current}), movie -> (binding=definitely_bound; tags={Movie}; defs={param:movie}; present={title, year}; points-to={boundary:external, boundary:revise}), year -> (binding=definitely_bound; tags={bool, int}; defs={param:year})
    # L11 pyhard[flow revise out] current -> (binding=definitely_unbound; tags={}; defs={unbound:current}), movie -> (binding=definitely_bound; tags={Movie}; defs={param:movie}; present={title, year}; points-to={boundary:external, boundary:revise}), year -> (binding=definitely_bound; tags={bool, int}; defs={param:year})
    # L11 pyhard[read revise.year@21] binding=definitely_bound
    # L11 pyhard[read revise.movie@5] binding=definitely_bound
    # L11 pyhard[type typed_dict_field_write] assert/assume conforms(Movie['year'], int); observed={bool, int}
    # L11 pyhard[shape typed_dict_field_write] assert/assume shape_Movie(movie); key='year'
    # L11 pyhard[dispatch movie['year']] assert/assume key in {Movie}
    # L11 pyhard[row {Movie}] typed_dict_field_write_checked; result={NoneType}
    movie["year"] = year
    # L12 pyhard[flow revise in] current -> (binding=definitely_unbound; tags={}; defs={unbound:current}), movie -> (binding=definitely_bound; tags={Movie}; defs={param:movie}; present={title, year}; points-to={boundary:external, boundary:revise}), year -> (binding=definitely_bound; tags={bool, int}; defs={param:year})
    # L12 pyhard[flow revise out] current -> (binding=definitely_unbound; tags={}; defs={unbound:current}), movie -> (binding=definitely_bound; tags={Movie}; defs={param:movie}; present={rating, title, year}; points-to={boundary:external, boundary:revise}), year -> (binding=definitely_bound; tags={bool, int}; defs={param:year})
    # L12 pyhard[read revise.movie@5] binding=definitely_bound
    # L12 pyhard[type typed_dict_update_field] assert/assume conforms(Movie['rating'], int); observed={int}
    # L12 pyhard[shape typed_dict_update] assert/assume shape_Movie(movie)
    # L12 pyhard[dispatch movie.update(rating=5)] assert/assume key in {Movie}
    # L12 pyhard[row {Movie}] invoke_typed_dict_method; owner=dict; label=pyhard.typeddict.Movie.update; result={NoneType}; specialized-by=literal key, presence, and argument contracts
    movie.update(rating=5)
    # L13 pyhard[flow revise in] current -> (binding=definitely_unbound; tags={}; defs={unbound:current}), movie -> (binding=definitely_bound; tags={Movie}; defs={param:movie}; present={rating, title, year}; points-to={boundary:external, boundary:revise}), year -> (binding=definitely_bound; tags={bool, int}; defs={param:year})
    # L13 pyhard[flow revise out] current -> (binding=definitely_unbound; tags={}; defs={unbound:current}), movie -> (binding=definitely_bound; tags={Movie}; defs={param:movie}; present={rating, title, year}; points-to={boundary:external, boundary:revise}), year -> (binding=definitely_bound; tags={bool, int}; defs={param:year})
    # L13 pyhard[read revise.movie@5] binding=definitely_bound
    # L13 pyhard[type typed_dict_setdefault] assert/assume conforms(Movie['rating'], int); observed={int}
    # L13 pyhard[shape typed_dict_setdefault] assert/assume shape_Movie(movie); key='rating'
    # L13 pyhard[dispatch movie.setdefault('rating', 0)] assert/assume key in {Movie}
    # L13 pyhard[row {Movie}] invoke_typed_dict_method; owner=dict; label=pyhard.typeddict.Movie.setdefault; result={int}; specialized-by=literal key, presence, and argument contracts
    movie.setdefault("rating", 0)
    # L14 pyhard[flow revise in] current -> (binding=definitely_unbound; tags={}; defs={unbound:current}), movie -> (binding=definitely_bound; tags={Movie}; defs={param:movie}; present={rating, title, year}; points-to={boundary:external, boundary:revise}), year -> (binding=definitely_bound; tags={bool, int}; defs={param:year})
    # L14 pyhard[flow revise out] current -> (binding=definitely_bound; tags={int}; defs={assignment:L14:C5}), movie -> (binding=definitely_bound; tags={Movie}; defs={param:movie}; present={rating, title, year}; points-to={boundary:external, boundary:revise}), year -> (binding=definitely_bound; tags={bool, int}; defs={param:year})
    # L14 pyhard[read revise.movie@15] binding=definitely_bound
    # L14 pyhard[dispatch movie.get('rating')] assert/assume key in {Movie}
    # L14 pyhard[row {Movie}] invoke_typed_dict_method; owner=dict; label=pyhard.typeddict.Movie.get; result={int}; specialized-by=literal key, presence, and argument contracts
    current = movie.get("rating")
    # L15 pyhard[flow revise in] current -> (binding=definitely_bound; tags={int}; defs={assignment:L14:C5}), movie -> (binding=definitely_bound; tags={Movie}; defs={param:movie}; present={rating, title, year}; points-to={boundary:external, boundary:revise}), year -> (binding=definitely_bound; tags={bool, int}; defs={param:year})
    # L15 pyhard[flow revise out] current -> (binding=definitely_bound; tags={int}; defs={assignment:L14:C5}), movie -> (binding=definitely_bound; tags={Movie}; defs={param:movie}; present={rating, title, year}; points-to={boundary:external, boundary:revise}), year -> (binding=definitely_bound; tags={bool, int}; defs={param:year})
    # L15 pyhard[read revise.current@8] binding=definitely_bound
    # L15 pyhard[dispatch current is None] assert/assume key in {bool}
    # L15 pyhard[row {bool}] exact_builtin_truth; result={bool}
    if current is None:
        # L16 pyhard[read revise.movie@16] binding=definitely_bound
        return movie["title"]
    # L17 pyhard[flow revise in] current -> (binding=definitely_bound; tags={int}; defs={assignment:L14:C5}), movie -> (binding=definitely_bound; tags={Movie}; defs={param:movie}; present={rating, title, year}; points-to={boundary:external, boundary:revise}), year -> (binding=definitely_bound; tags={bool, int}; defs={param:year})
    # L17 pyhard[flow revise out:return] $result -> (binding=definitely_bound; tags={str}; defs={return}), current -> (binding=definitely_bound; tags={int}; defs={assignment:L14:C5}), movie -> (binding=definitely_bound; tags={Movie}; defs={param:movie}; present={rating, title, year}; points-to={boundary:external, boundary:revise}), year -> (binding=definitely_bound; tags={bool, int}; defs={param:year})
    # L17 pyhard[read revise.movie@12] binding=definitely_bound
    # L17 pyhard[type return] assert/assume conforms(result, str); observed={str}
    # L17 pyhard[dispatch movie['title']] assert/assume key in {Movie}
    # L17 pyhard[row {Movie}] typed_dict_field_read; result={str}
    return movie["title"]

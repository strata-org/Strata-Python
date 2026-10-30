# A `"k" in c` or `"k" not in c` whose container does not translate gives one warning per cause.
def f(x: int) -> None:
    assert "k" not in g(x), "no k"
    assert "k" in g(x), "k"

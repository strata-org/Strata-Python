# The parts of an f-string message keep their source text.
def f(s: str) -> None:
    assert len(s) >= 1, f"got {len(s)} for {s.upper()}"

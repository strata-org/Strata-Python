def wrap():
    try:
        raise ValueError("inner")
    except ValueError as exc:
        raise KeyError("outer") from exc

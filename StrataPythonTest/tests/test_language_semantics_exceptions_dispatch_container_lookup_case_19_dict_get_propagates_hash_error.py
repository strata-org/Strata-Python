# dict.get propagates exceptions from key hashing.
"""dict.get propagates exceptions from key hashing."""


class BadKey:
    def __hash__(self):
        raise KeyError("hash failed")


try:
    {}.get(BadKey(), "fallback")
except Exception as error:
    RESULT = type(error).__name__
else:
    RESULT = "not raised"

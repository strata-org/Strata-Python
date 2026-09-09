# Outside the fragment on many axes at once: a realistic-looking
# script whose every idiom breaks a different admission rule. The
# checker must report ALL of them in one pass (Validation pattern),
# not stop at the first.
import os
from functools import lru_cache


@lru_cache(maxsize=None)
def fetch(url):
    with open(url) as f:
        data = f.read()
    handler = getattr(os, "listdir")
    result = eval("1 + 1")
    clean = lambda s: s.strip()
    return clean(data), handler, result


class Meta(type):
    pass


list = [1, 2, 3]

# Under `from __future__ import annotations`, CPython 3.12 stores each annotation's source
# text unevaluated, which the translator rejects for now.  The declared shape still states
# the annotation as if it were evaluated, with its private name mangled.
from __future__ import annotations


class Node:
    next: Node
    prev: __T

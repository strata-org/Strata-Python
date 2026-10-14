# Under `from __future__ import annotations`, CPython 3.12 stores each annotation's source
# text unevaluated, which the translator rejects for now.
from __future__ import annotations


class Node:
    next: Node

# An invariant that doesn't translate keeps its source text, with no formula; the text keeps
# its non-ASCII characters.
@invariant(lambda self: self.x.bit_length() > 0)
@invariant(lambda self: self.name != "é")
class C:
    x: int
    name: str

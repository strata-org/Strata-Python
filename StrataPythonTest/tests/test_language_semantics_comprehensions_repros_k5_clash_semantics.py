# The Python semantics the encoding must match. Run with plain python3 to see them.
class K:
    """__eq__/__hash__ on n only, but carries a tag so we can see WHICH object survived."""
    def __init__(s, n, tag): s.n, s.tag = n, tag
    def __hash__(s): return hash(s.n)
    def __eq__(s, o): return isinstance(o, K) and s.n == o.n
    def __repr__(s): return f"K({s.n},{s.tag})"

pairs = [(K(1, 'first'), 'v1'), (K(2, 'x'), 'v2'), (K(1, 'second'), 'v3')]
d = {k: v for k, v in pairs}
assert len(d) == 2
assert [x for x in d if x.n == 1][0].tag == 'first'   # KEY   <- FIRST occurrence
assert d[K(1, '?')] == 'v3'                           # VALUE <- LAST  occurrence
assert list(d)[0].tag == 'first'                      # ORDER <- FIRST occurrence

s = {K(1, 'first'), K(2, 'x'), K(1, 'second')}
assert len(s) == 2
assert [x for x in s if x.n == 1][0].tag == 'first'   # ELEMENT <- FIRST occurrence

xs = [1, 1, 1, 2, 2, 3]
assert len([x for x in xs]) == 6      # list: no dedup
assert len({x for x in xs}) == 3      # set:  dedup
assert len({x: x for x in xs}) == 3   # dict: dedup

# ---- ORDER. The two containers differ, and this is the fact that decides whether
# the list case's monotonicity axiom may be reused.
#
# dict IS insertion-ordered (guaranteed since 3.7) -> monotonicity on the
# first-writer witness is SOUND.
assert list({k: k for k in [3, 1, 2]}) == [3, 1, 2]

# set is NOT: slot order follows the hash, which the language leaves unspecified,
# so NO ordering may be assumed. This is why ex6_setcomp.c carries dedup +
# minimality instead of monotonicity; see ex6_order_unsound.c.
assert list({3, 1, 2}) == [1, 2, 3]        # small ints hash to themselves
assert list({3, 1, 2})[0] != 3             # the FIRST INSERTED is not in slot 0

# ---- last-writer-wins for values, the canonical case (ex7_maximality.c)
assert {x % 2: x for x in range(4)} == {0: 2, 1: 3}
assert {x % 2: x for x in range(4)}[0] == 2     # x=0 wrote first, x=2 wrote last

print("all Python clash-semantics assertions hold")

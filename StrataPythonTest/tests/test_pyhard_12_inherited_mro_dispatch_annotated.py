# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
class Base:
    # L2 pyhard[summary Base.inherited] returns={str}; escapes={}
    def inherited(self) -> str:
        # L3 pyhard[flow Base.inherited in] self -> (binding=definitely_bound; tags={Base}; defs={param:self}; points-to={alloc:L15:C36, alloc:L16:C12, boundary:Base.inherited, boundary:Leaf.local, boundary:external, boundary:use_leaf})
        # L3 pyhard[flow Base.inherited out:return] $result -> (binding=definitely_bound; tags={str}; defs={return}), self -> (binding=definitely_bound; tags={Base}; defs={param:self}; points-to={alloc:L15:C36, alloc:L16:C12, boundary:Base.inherited, boundary:Leaf.local, boundary:external, boundary:use_leaf})
        # L3 pyhard[type return] assert/assume conforms(result, str); observed={str}
        return "base"


class Middle(Base):
    pass


class Leaf(Middle):
    # L11 pyhard[summary Leaf.local] returns={int}; escapes={}
    def local(self) -> int:
        # L12 pyhard[flow Leaf.local in] self -> (binding=definitely_bound; tags={Leaf}; defs={param:self}; points-to={alloc:L15:C36, alloc:L16:C12, boundary:Base.inherited, boundary:Leaf.local, boundary:external, boundary:use_leaf})
        # L12 pyhard[flow Leaf.local out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), self -> (binding=definitely_bound; tags={Leaf}; defs={param:self}; points-to={alloc:L15:C36, alloc:L16:C12, boundary:Base.inherited, boundary:Leaf.local, boundary:external, boundary:use_leaf})
        # L12 pyhard[type return] assert/assume conforms(result, int); observed={int}
        return 3


# L15 pyhard[summary use_leaf] returns={tuple}; escapes={}
# L15 pyhard[type parameter] assert/assume conforms(value, Leaf); boundary nondet over 19 closed tags
def use_leaf(value: Leaf) -> tuple[str, int]:
    # L16 pyhard[flow use_leaf in] value -> (binding=definitely_bound; tags={Leaf}; defs={param:value}; points-to={alloc:L15:C36, alloc:L16:C12, boundary:Base.inherited, boundary:Leaf.local, boundary:external, boundary:use_leaf})
    # L16 pyhard[flow use_leaf out:return] $result -> (binding=definitely_bound; tags={tuple}; defs={return}), value -> (binding=definitely_bound; tags={Leaf}; defs={param:value}; points-to={alloc:L15:C36, alloc:L16:C12, boundary:Base.inherited, boundary:Leaf.local, boundary:external, boundary:use_leaf})
    # L16 pyhard[read use_leaf.value@12] binding=definitely_bound
    # L16 pyhard[read use_leaf.value@31] binding=definitely_bound
    # L16 pyhard[type return] assert/assume conforms(result, tuple[str, int]); observed={tuple}
    # L16 pyhard[dispatch value.inherited()] assert/assume key in {Leaf}
    # L16 pyhard[row {Leaf}] invoke_method; owner=Base; label=Base.inherited; result={str}
    # L16 pyhard[dispatch value.local()] assert/assume key in {Leaf}
    # L16 pyhard[row {Leaf}] invoke_method; owner=Leaf; label=Leaf.local; result={int}
    return value.inherited(), value.local()

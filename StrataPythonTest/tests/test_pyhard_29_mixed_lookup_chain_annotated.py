# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
from typing import TypedDict


class Branch:
    b: int

    # L7 pyhard[summary Branch.__init__] returns={NoneType}; escapes={}
    # L7 pyhard[type parameter] assert/assume conforms(b, int); boundary nondet over 20 closed tags
    def __init__(self, b: int):
        # L8 pyhard[flow Branch.__init__ in] b -> (binding=definitely_bound; tags={bool, int}; defs={param:b}), self -> (binding=definitely_bound; tags={Branch}; defs={param:self}; points-to={boundary:Branch.__init__, boundary:Record.__init__, boundary:Root.__init__, boundary:combine, boundary:external})
        # L8 pyhard[flow Branch.__init__ out] b -> (binding=definitely_bound; tags={bool, int}; defs={param:b}), self -> (binding=definitely_bound; tags={Branch}; defs={param:self}; points-to={boundary:Branch.__init__, boundary:Record.__init__, boundary:Root.__init__, boundary:combine, boundary:external})
        # L8 pyhard[read Branch.__init__.b@18] binding=definitely_bound
        # L8 pyhard[read Branch.__init__.self@9] binding=definitely_bound
        # L8 pyhard[type field_write] assert/assume conforms(Branch.b, int); observed={bool, int}
        # L8 pyhard[dispatch self.b] assert/assume key in {Branch}
        # L8 pyhard[row {Branch}] store_declared_field; owner=Branch; result={NoneType}
        self.b = b


class Root:
    a: Branch

    # L14 pyhard[summary Root.__init__] returns={NoneType}; escapes={}
    # L14 pyhard[type parameter] assert/assume conforms(a, Branch); boundary nondet over 20 closed tags
    def __init__(self, a: Branch):
        # L15 pyhard[flow Root.__init__ in] a -> (binding=definitely_bound; tags={Branch}; defs={param:a}; points-to={boundary:Branch.__init__, boundary:Record.__init__, boundary:Root.__init__, boundary:combine, boundary:external}), self -> (binding=definitely_bound; tags={Root}; defs={param:self}; points-to={boundary:Branch.__init__, boundary:Record.__init__, boundary:Root.__init__, boundary:combine, boundary:external}); aliases may={a~self} must={}
        # L15 pyhard[flow Root.__init__ out] a -> (binding=definitely_bound; tags={Branch}; defs={param:a}; points-to={boundary:Branch.__init__, boundary:Record.__init__, boundary:Root.__init__, boundary:combine, boundary:external}), self -> (binding=definitely_bound; tags={Root}; defs={param:self}; points-to={boundary:Branch.__init__, boundary:Record.__init__, boundary:Root.__init__, boundary:combine, boundary:external}); aliases may={a~self} must={}
        # L15 pyhard[read Root.__init__.a@18] binding=definitely_bound
        # L15 pyhard[read Root.__init__.self@9] binding=definitely_bound
        # L15 pyhard[type field_write] assert/assume conforms(Root.a, Branch); observed={Branch}
        # L15 pyhard[dispatch self.a] assert/assume key in {Root}
        # L15 pyhard[row {Root}] store_declared_field; owner=Root; result={NoneType}
        self.a = a


class Record:
    field: int

    # L21 pyhard[summary Record.__init__] returns={NoneType}; escapes={}
    # L21 pyhard[type parameter] assert/assume conforms(field, int); boundary nondet over 20 closed tags
    def __init__(self, field: int):
        # L22 pyhard[flow Record.__init__ in] field -> (binding=definitely_bound; tags={bool, int}; defs={param:field}), self -> (binding=definitely_bound; tags={Record}; defs={param:self}; points-to={boundary:Branch.__init__, boundary:Record.__init__, boundary:Root.__init__, boundary:combine, boundary:external})
        # L22 pyhard[flow Record.__init__ out] field -> (binding=definitely_bound; tags={bool, int}; defs={param:field}), self -> (binding=definitely_bound; tags={Record}; defs={param:self}; points-to={boundary:Branch.__init__, boundary:Record.__init__, boundary:Root.__init__, boundary:combine, boundary:external})
        # L22 pyhard[read Record.__init__.field@22] binding=definitely_bound
        # L22 pyhard[read Record.__init__.self@9] binding=definitely_bound
        # L22 pyhard[type field_write] assert/assume conforms(Record.field, int); observed={bool, int}
        # L22 pyhard[dispatch self.field] assert/assume key in {Record}
        # L22 pyhard[row {Record}] store_declared_field; owner=Record; result={NoneType}
        self.field = field


class Records(TypedDict):
    key: Record


# L29 pyhard[summary combine] returns={int}; escapes={}
# L29 pyhard[type parameter] assert/assume conforms(x, Root); boundary nondet over 20 closed tags
# L29 pyhard[type parameter] assert/assume conforms(d, Records); boundary nondet over 20 closed tags
# L29 pyhard[shape typed_dict_parameter] assert/assume shape_Records(d)
def combine(x: Root, d: Records) -> int:
    # L30 pyhard[flow combine in] d -> (binding=definitely_bound; tags={Records}; defs={param:d}; present={key}; points-to={boundary:Branch.__init__, boundary:Record.__init__, boundary:Root.__init__, boundary:combine, boundary:external}), x -> (binding=definitely_bound; tags={Root}; defs={param:x}; points-to={boundary:Branch.__init__, boundary:Record.__init__, boundary:Root.__init__, boundary:combine, boundary:external}); aliases may={d~x} must={}
    # L30 pyhard[flow combine out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), d -> (binding=definitely_bound; tags={Records}; defs={param:d}; present={key}; points-to={boundary:Branch.__init__, boundary:Record.__init__, boundary:Root.__init__, boundary:combine, boundary:external}), x -> (binding=definitely_bound; tags={Root}; defs={param:x}; points-to={boundary:Branch.__init__, boundary:Record.__init__, boundary:Root.__init__, boundary:combine, boundary:external}); aliases may={d~x} must={}
    # L30 pyhard[read combine.x@12] binding=definitely_bound
    # L30 pyhard[read combine.d@20] binding=definitely_bound
    # L30 pyhard[type return] assert/assume conforms(result, int); observed={int}
    # L30 pyhard[dispatch x.a] assert/assume key in {Root}
    # L30 pyhard[row {Root}] read_declared_field; owner=Root; result={Branch}
    # L30 pyhard[dispatch x.a.b] assert/assume key in {Branch}
    # L30 pyhard[row {Branch}] read_declared_field; owner=Branch; result={bool, int}
    # L30 pyhard[dispatch d['key']] assert/assume key in {Records}
    # L30 pyhard[row {Records}] typed_dict_field_read; result={Record}
    # L30 pyhard[dispatch d['key'].field] assert/assume key in {Record}
    # L30 pyhard[row {Record}] read_declared_field; owner=Record; result={bool, int}
    # L30 pyhard[dispatch x.a.b + d['key'].field] assert/assume key in {(bool, bool), (bool, int), (int, bool), (int, int)}
    # L30 pyhard[row {(bool, bool), (bool, int), (int, bool), (int, int)}] binary_protocol; result={int}; terminal=certified_builtin_total
    return x.a.b + d["key"].field

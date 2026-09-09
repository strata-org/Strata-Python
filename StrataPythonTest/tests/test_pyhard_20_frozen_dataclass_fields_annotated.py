# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
from dataclasses import dataclass


@dataclass(frozen=True)
class Key:
    region: str
    shard: int


# L10 pyhard[summary make_key] returns={Key}; escapes={}
# L10 pyhard[type parameter] assert/assume conforms(region, str); boundary nondet over 17 closed tags
# L10 pyhard[type parameter] assert/assume conforms(shard, int); boundary nondet over 17 closed tags
def make_key(region: str, shard: int) -> Key:
    # L11 pyhard[flow make_key in] region -> (binding=definitely_bound; tags={str}; defs={param:region}), shard -> (binding=definitely_bound; tags={bool, int}; defs={param:shard})
    # L11 pyhard[flow make_key out:return] $result -> (binding=definitely_bound; tags={Key}; defs={return}), region -> (binding=definitely_bound; tags={str}; defs={param:region}), shard -> (binding=definitely_bound; tags={bool, int}; defs={param:shard})
    # L11 pyhard[read make_key.region@23] binding=definitely_bound
    # L11 pyhard[read make_key.shard@37] binding=definitely_bound
    # L11 pyhard[type return] assert/assume conforms(result, Key); observed={Key}
    return Key(region=region, shard=shard)


# L14 pyhard[summary read_key] returns={tuple}; escapes={}
# L14 pyhard[type parameter] assert/assume conforms(key, Key); boundary nondet over 17 closed tags
def read_key(key: Key) -> tuple[str, int]:
    # L15 pyhard[flow read_key in] key -> (binding=definitely_bound; tags={Key}; defs={param:key}; points-to={alloc:L11:C12, alloc:L14:C33, alloc:L15:C12, boundary:external, boundary:make_key, boundary:read_key})
    # L15 pyhard[flow read_key out:return] $result -> (binding=definitely_bound; tags={tuple}; defs={return}), key -> (binding=definitely_bound; tags={Key}; defs={param:key}; points-to={alloc:L11:C12, alloc:L14:C33, alloc:L15:C12, boundary:external, boundary:make_key, boundary:read_key})
    # L15 pyhard[read read_key.key@12] binding=definitely_bound
    # L15 pyhard[read read_key.key@24] binding=definitely_bound
    # L15 pyhard[type return] assert/assume conforms(result, tuple[str, int]); observed={tuple}
    # L15 pyhard[dispatch key.region] assert/assume key in {Key}
    # L15 pyhard[row {Key}] read_declared_field; owner=Key; result={str}
    # L15 pyhard[dispatch key.shard] assert/assume key in {Key}
    # L15 pyhard[row {Key}] read_declared_field; owner=Key; result={bool, int}
    return key.region, key.shard

from dataclasses import dataclass


@dataclass(frozen=True)
class Key:
    region: str
    shard: int


def make_key(region: str, shard: int) -> Key:
    return Key(region=region, shard=shard)


def read_key(key: Key) -> tuple[str, int]:
    return key.region, key.shard

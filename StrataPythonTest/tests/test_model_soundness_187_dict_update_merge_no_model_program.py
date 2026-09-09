# `dict.update(other)` — no merge operation; requires iterating other and
# setting each key (blocked by finding 082)
"""
`dict.update(other)` merges another dict into the current one.
Keys from `other` overwrite existing keys. Returns None.

Under pure association-list semantics, update must:
1. Prepend all key-value pairs from `other` onto `self`
2. Rebind the dict variable
3. Return None as expression value

But there's no `DictStrAny_update` operation. And the association-list
shadowing problem (finding 082) means naive prepending creates duplicates
that break `len()` and iteration.

Uses ONLY confirmed-accepted constructs: dict, update, str, int.
"""


def merge_dicts() -> dict[str, int]:
    base: dict[str, int] = {"a": 1, "b": 2}
    extra: dict[str, int] = {"b": 99, "c": 3}
    base.update(extra)
    # "b" is overwritten to 99, "c" is added
    return base


def update_returns_none() -> bool:
    d: dict[str, int] = {"x": 1}
    result = d.update({"y": 2})
    return result is None


def update_overwrites() -> int:
    d: dict[str, int] = {"key": 10}
    d.update({"key": 20})
    return d["key"]  # 20 (overwritten)


def update_adds_new() -> int:
    d: dict[str, int] = {"a": 1}
    d.update({"b": 2, "c": 3})
    return len(d)  # 3


def build_config() -> dict[str, int]:
    """Common pattern: defaults + overrides."""
    defaults: dict[str, int] = {"timeout": 30, "retries": 3, "port": 8080}
    overrides: dict[str, int] = {"timeout": 60, "port": 9090}
    config: dict[str, int] = {}
    config.update(defaults)
    config.update(overrides)  # overrides win
    return config


def main() -> None:
    # Merge
    merged: dict[str, int] = merge_dicts()
    assert merged["a"] == 1
    assert merged["b"] == 99  # overwritten
    assert merged["c"] == 3

    # Returns None
    assert update_returns_none() == True

    # Overwrites
    assert update_overwrites() == 20

    # Adds new keys
    assert update_adds_new() == 3

    # Config pattern
    config: dict[str, int] = build_config()
    assert config["timeout"] == 60  # overridden
    assert config["retries"] == 3   # from defaults
    assert config["port"] == 9090   # overridden

    print(merged["b"], update_adds_new(), config["timeout"])


main()

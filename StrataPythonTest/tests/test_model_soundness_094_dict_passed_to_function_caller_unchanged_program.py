# Dict passed to function — caller's dict unchanged under value semantics;
# `add_entry(d, k, v)` invisible to caller
"""
When a dict is passed to a function that modifies it (`d[k] = v`),
the caller's dict is unchanged under pure-function value semantics.
In CPython, dicts are passed by reference — the caller sees the change.

This is the dict-specific instance of finding 005 (mutable container
passed to function). The divergence is that the function's modifications
are invisible to the caller.
"""


def add_entry(d: dict[str, int], key: str, value: int) -> None:
    d[key] = value
    # CPython: modifies the dict in place; caller sees it
    # Model: modifies a local copy; caller's dict unchanged


def remove_and_add(d: dict[str, int]) -> None:
    d["new"] = 99
    d["x"] = d["x"] + 1  # increment existing key


def build_config(d: dict[str, int]) -> None:
    d["timeout"] = 30
    d["retries"] = 3
    d["port"] = 8080


def main() -> None:
    # Pass dict to function that adds a key
    data: dict[str, int] = {"a": 1, "b": 2}
    add_entry(data, "c", 3)
    # CPython: data = {"a": 1, "b": 2, "c": 3}
    # Model: data = {"a": 1, "b": 2} (unchanged)
    assert "c" in data
    assert data["c"] == 3
    assert len(data) == 3

    # Pass dict to function that modifies existing key
    counters: dict[str, int] = {"x": 10, "y": 20}
    remove_and_add(counters)
    # CPython: counters = {"x": 11, "y": 20, "new": 99}
    # Model: counters = {"x": 10, "y": 20} (unchanged)
    assert counters["x"] == 11
    assert "new" in counters

    # Build config by passing empty dict
    cfg: dict[str, int] = {}
    build_config(cfg)
    # CPython: cfg = {"timeout": 30, "retries": 3, "port": 8080}
    # Model: cfg = {} (unchanged)
    assert cfg["timeout"] == 30
    assert len(cfg) == 3

    print(data, counters["x"], len(cfg))


main()

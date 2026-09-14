#!/usr/bin/env python3
"""Generate CPython-vs-analyzer scenarios across the callable surface.

The hand-written corpus pins one or two cases per rule. This generator covers
the invalid-argument and mixed-value dimensions mechanically: every method of
every admitted receiver type is called with argument tuples drawn from a pool
of fragment-expressible literals, CPython decides the outcome, and the
conformance driver checks that the analyzer includes it.

    python3.13 tests/callable_rule_fuzz.py -o tests/callable_rule_fuzz.json
"""

from __future__ import annotations

import argparse
import json
import os

import sys as _sys, os as _os
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
import paths
paths.on_path()
HERE = paths.DATA

# Receiver expressions, one per admitted runtime tag.
RECEIVERS = {
    "list": "[1, 2]",
    "dict": "{'a': 1}",
    "set": "{1, 2}",
    "tuple": "(1, 2)",
    "str": "'ab'",
    "range": "range(3)",
}

METHODS = {
    "list": ["append", "clear", "copy", "count", "extend", "index", "insert",
             "pop", "remove", "reverse", "sort"],
    "dict": ["clear", "copy", "get", "items", "keys", "pop", "popitem",
             "setdefault", "update", "values"],
    "set": ["add", "clear", "copy", "difference", "difference_update",
            "discard", "intersection", "intersection_update", "isdisjoint",
            "issubset", "issuperset", "pop", "remove",
            "symmetric_difference", "symmetric_difference_update", "union",
            "update"],
    "tuple": ["count", "index"],
    "range": ["count", "index"],
    "str": ["capitalize", "casefold", "center", "count", "endswith",
            "expandtabs", "find", "index", "isalnum", "isalpha", "isascii",
            "isdecimal", "isdigit", "isidentifier", "islower", "isnumeric",
            "isprintable", "isspace", "istitle", "isupper", "join", "ljust",
            "lower", "lstrip", "partition", "removeprefix", "removesuffix",
            "replace", "rfind", "rindex", "rjust", "rpartition", "rsplit",
            "rstrip", "split", "splitlines", "startswith", "strip",
            "swapcase", "title", "upper", "zfill"],
}

FUNCTIONS = {
    "len": 1, "str": 1, "repr": 1, "isinstance": 2, "range": 3, "iter": 1,
    "next": 2, "list": 1, "tuple": 1, "set": 1, "dict": 1,
}

# Fragment-expressible literals spanning every tag the rules dispatch on.
POOL = [
    "0", "1", "True", "'x'", "''", "'ab'", "1.5", "None",
    "[]", "[1]", "[[1]]", "()", "(1,)", "{}", "{'a': 1}", "set()", "{1}",
    "[('a', 1)]", "[(1,)]", "range(2)",
]

# Arity-2 pairs are sampled rather than crossed to keep the corpus bounded.
PAIRS = [
    ("'a'", "'b'"), ("'a'", "0"), ("0", "'a'"), ("0", "1"), ("[1]", "0"),
    ("'a'", "None"), ("None", "'a'"), ("{}", "0"), ("1", "[1]"),
    ("'ab'", "''"), ("''", "'a'"), ("[1]", "[2]"),
]


def scenario(rule_key: str, name: str, setup: str, call: str) -> dict:
    return {
        "id": f"fuzz_{rule_key.replace('.', '_')}_{name}",
        "rule_key": rule_key,
        "scenario": name,
        "categories": ["cpython_evidence", "invalid"],
        "obligations": ["raised-class", "raise-point-state"],
        "execution": {"setup": setup, "call": call, "roots": ["receiver"]},
        "expect": {"outcome": {"kind": "generated", "type": ""}},
    }


NAMES = {
    "0": "zero", "1": "one", "True": "true", "'x'": "strx", "''": "emptystr",
    "'ab'": "strab", "1.5": "float", "None": "none", "[]": "emptylist",
    "[1]": "list1", "[[1]]": "nestedlist", "()": "emptytuple",
    "(1,)": "tuple1", "{}": "emptydict", "{'a': 1}": "dict1",
    "set()": "emptyset", "{1}": "set1", "[('a', 1)]": "pairs",
    "[(1,)]": "shortpair", "range(2)": "range",
}


def sanitize(expression: str) -> str:
    """A unique, readable name per literal expression."""
    if expression in NAMES:
        return NAMES[expression]
    table = str.maketrans({c: "" for c in " '\"[](){},.:-"})
    return "lit" + expression.translate(table)


def generate() -> list[dict]:
    scenarios: list[dict] = []
    for tag, receiver in RECEIVERS.items():
        for method in METHODS.get(tag, []):
            base = f"{tag}.{method}"
            setup = f"receiver = {receiver}"
            scenarios.append(
                scenario(base, "arity0", setup, f"receiver.{method}()")
            )
            for value in POOL:
                scenarios.append(
                    scenario(
                        base,
                        f"arg_{sanitize(value)}",
                        f"{setup}\narg0 = {value}",
                        f"receiver.{method}(arg0)",
                    )
                )
            for left, right in PAIRS:
                scenarios.append(
                    scenario(
                        base,
                        f"args_{sanitize(left)}_{sanitize(right)}",
                        f"{setup}\narg0 = {left}\narg1 = {right}",
                        f"receiver.{method}(arg0, arg1)",
                    )
                )
    for name, arity in FUNCTIONS.items():
        for value in POOL:
            scenarios.append(
                scenario(
                    name,
                    f"arg_{sanitize(value)}",
                    f"arg0 = {value}",
                    f"{name}(arg0)",
                )
            )
        if arity >= 2:
            for left, right in PAIRS:
                scenarios.append(
                    scenario(
                        name,
                        f"args_{sanitize(left)}_{sanitize(right)}",
                        f"arg0 = {left}\narg1 = {right}",
                        f"{name}(arg0, arg1)",
                    )
                )
    return scenarios


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "-o", "--output", default=os.path.join(HERE, "callable_rule_fuzz.json")
    )
    arguments = parser.parse_args()
    scenarios = generate()
    payload = {
        "schema_version": 1,
        "note": "generated by callable_rule_fuzz.py; regenerate rather than edit",
        "scenarios": scenarios,
    }
    with open(arguments.output, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=1, sort_keys=True)
        handle.write("\n")
    print(f"wrote {len(scenarios)} scenarios to {arguments.output}")


if __name__ == "__main__":
    main()

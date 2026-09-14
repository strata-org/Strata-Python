#!/usr/bin/env python3
"""Mine CPython binary-operator behavior over the Pylate value universe.

The default report groups concrete observations by:

    operator x left runtime tag x right runtime tag

Each cell retains every observed return type and exception class, with
representative inputs. A cell with more than one outcome is direct evidence
that a tag-pair dispatch row needs value or shape guards.

Use --full to include every concrete run in the JSON output.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import operator
import os
import platform
import sys
from collections import defaultdict
from dataclasses import dataclass
from typing import Any, Callable


Factory = Callable[[], object]
BinaryOperator = Callable[[object, object], object]


@dataclass(frozen=True)
class Sample:
    tag: str
    label: str
    make: Factory


def const(value: object) -> Factory:
    return lambda: value


def make_generator() -> object:
    return (x for x in (1, 2))


SAMPLES = [
    Sample("none", "None", const(None)),
    Sample("bool", "False", const(False)),
    Sample("bool", "True", const(True)),
    Sample("int", "-2", const(-2)),
    Sample("int", "0", const(0)),
    Sample("int", "2", const(2)),
    Sample("int", "65", const(65)),
    Sample("int", "1000", const(1000)),
    Sample("float", "-2.5", const(-2.5)),
    Sample("float", "0.0", const(0.0)),
    Sample("float", "2.5", const(2.5)),
    Sample("float", "1e308", const(1e308)),
    Sample("float", "float('inf')", const(float("inf"))),
    Sample("float", "float('nan')", const(float("nan"))),
    Sample("str", "''", const("")),
    Sample("str", "'x'", const("x")),
    Sample("str", "'ab'", const("ab")),
    Sample("str", "'%s'", const("%s")),
    Sample("str", "'%r'", const("%r")),
    Sample("str", "'%a'", const("%a")),
    Sample("str", "'%d'", const("%d")),
    Sample("str", "'%i'", const("%i")),
    Sample("str", "'%u'", const("%u")),
    Sample("str", "'%o'", const("%o")),
    Sample("str", "'%x'", const("%x")),
    Sample("str", "'%f'", const("%f")),
    Sample("str", "'%e'", const("%e")),
    Sample("str", "'%g'", const("%g")),
    Sample("str", "'%(x)s'", const("%(x)s")),
    Sample("str", "'%(x)d'", const("%(x)d")),
    Sample("str", "'%'", const("%")),
    Sample("str", "'%%'", const("%%")),
    Sample("str", "'%*s'", const("%*s")),
    Sample("str", "'%.*s'", const("%.*s")),
    Sample("str", "'%c'", const("%c")),
    Sample("list", "[]", const([])),
    Sample("list", "[1]", const([1])),
    Sample("dict", "{}", const({})),
    Sample("dict", "{'x': 1}", const({"x": 1})),
    Sample("set", "set()", const(set())),
    Sample("set", "{1}", const({1})),
    Sample("tuple", "()", const(())),
    Sample("tuple", "(1,)", const((1,))),
    Sample("tuple", "(1, 2)", const((1, 2))),
    Sample("range", "range(0)", const(range(0))),
    Sample("range", "range(2)", const(range(2))),
    Sample("dict_view", "{}.keys()", lambda: {}.keys()),
    Sample("dict_view", "{'x': 1}.keys()", lambda: {"x": 1}.keys()),
    Sample("dict_view", "{}.items()", lambda: {}.items()),
    Sample("dict_view", "{'x': 1}.items()", lambda: {"x": 1}.items()),
    Sample("dict_view", "{}.values()", lambda: {}.values()),
    Sample("dict_view", "{'x': 1}.values()", lambda: {"x": 1}.values()),
    Sample("gen", "(x for x in (1, 2))", make_generator),
    Sample("obj", "object()", object),
    Sample("type", "int", const(int)),
    Sample("func", "(lambda: None)", lambda: (lambda: None)),
    Sample("NotImplemented", "NotImplemented", const(NotImplemented)),
]


OPERATORS: list[tuple[str, str, BinaryOperator]] = [
    ("add", "+", operator.add),
    ("sub", "-", operator.sub),
    ("mul", "*", operator.mul),
    ("truediv", "/", operator.truediv),
    ("floordiv", "//", operator.floordiv),
    ("mod", "%", operator.mod),
    ("pow", "**", operator.pow),
    ("lshift", "<<", operator.lshift),
    ("rshift", ">>", operator.rshift),
    ("and", "&", operator.and_),
    ("xor", "^", operator.xor),
    ("or", "|", operator.or_),
]


def clipped_repr(value: object, limit: int = 120) -> str:
    text = repr(value)
    if len(text) <= limit:
        return text
    return text[: limit - 3] + "..."


def observe(op: BinaryOperator, left: Sample, right: Sample) -> dict[str, Any]:
    try:
        result = op(left.make(), right.make())
        return {
            "kind": "return",
            "class": type(result).__name__,
            "value": clipped_repr(result),
        }
    except BaseException as exc:
        return {
            "kind": "raise",
            "class": type(exc).__name__,
            "message": str(exc),
        }


def outcome_key(outcome: dict[str, Any]) -> str:
    return f"{outcome['kind']}:{outcome['class']}"


def trace_protocol_scenarios() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []

    def run(name: str, thunk: Callable[[list[str]], object]) -> None:
        events: list[str] = []
        try:
            result = thunk(events)
            outcome = {
                "kind": "return",
                "class": type(result).__name__,
                "value": clipped_repr(result),
            }
        except BaseException as exc:
            outcome = {
                "kind": "raise",
                "class": type(exc).__name__,
                "message": str(exc),
            }
        rows.append({"name": name, "events": events, "outcome": outcome})

    def forward_wins(events: list[str]) -> object:
        class Left:
            def __add__(self, other: object) -> object:
                events.append("Left.__add__")
                return "forward"

        class Right:
            def __radd__(self, other: object) -> object:
                events.append("Right.__radd__")
                return "reflected"

        return Left() + Right()

    def notimpl_falls_through(events: list[str]) -> object:
        class Left:
            def __add__(self, other: object) -> object:
                events.append("Left.__add__")
                return NotImplemented

        class Right:
            def __radd__(self, other: object) -> object:
                events.append("Right.__radd__")
                return "reflected"

        return Left() + Right()

    def forward_raise_stops(events: list[str]) -> object:
        class Left:
            def __add__(self, other: object) -> object:
                events.append("Left.__add__")
                raise LookupError("forward")

        class Right:
            def __radd__(self, other: object) -> object:
                events.append("Right.__radd__")
                return "unreachable"

        return Left() + Right()

    def same_type_skips_reflected(events: list[str]) -> object:
        class Both:
            def __add__(self, other: object) -> object:
                events.append("Both.__add__")
                return NotImplemented

            def __radd__(self, other: object) -> object:
                events.append("Both.__radd__")
                return "unreachable"

        return Both() + Both()

    def subclass_reflected_first(events: list[str]) -> object:
        class Base:
            def __add__(self, other: object) -> object:
                events.append("Base.__add__")
                return "forward"

        class Sub(Base):
            def __radd__(self, other: object) -> object:
                events.append("Sub.__radd__")
                return "reflected"

        return Base() + Sub()

    def subclass_notimpl_then_forward(events: list[str]) -> object:
        class Base:
            def __add__(self, other: object) -> object:
                events.append("Base.__add__")
                return "forward"

        class Sub(Base):
            def __radd__(self, other: object) -> object:
                events.append("Sub.__radd__")
                return NotImplemented

        return Base() + Sub()

    def builtin_numeric_reflected(events: list[str]) -> object:
        class Right:
            def __radd__(self, other: object) -> object:
                events.append("Right.__radd__")
                return 7

        return 1 + Right()

    def builtin_sequence_reflected(events: list[str]) -> object:
        class Right:
            def __radd__(self, other: object) -> object:
                events.append("Right.__radd__")
                return 7

        return [1] + Right()

    def builtin_sequence_fallback(events: list[str]) -> object:
        class Right:
            def __radd__(self, other: object) -> object:
                events.append("Right.__radd__")
                return NotImplemented

        return [1] + Right()

    def str_mod_stops_before_reflected(events: list[str]) -> object:
        class Right:
            def __rmod__(self, other: object) -> object:
                events.append("Right.__rmod__")
                return "reflected"

        return "plain" % Right()

    def custom_mod_falls_through(events: list[str]) -> object:
        class Left:
            def __mod__(self, other: object) -> object:
                events.append("Left.__mod__")
                return NotImplemented

        class Right:
            def __rmod__(self, other: object) -> object:
                events.append("Right.__rmod__")
                return "reflected"

        return Left() % Right()

    scenarios = [
        ("forward result suppresses reflected", forward_wins),
        ("NotImplemented falls through to reflected", notimpl_falls_through),
        ("forward exception suppresses reflected", forward_raise_stops),
        ("same runtime type skips reflected", same_type_skips_reflected),
        ("proper subclass reflected override runs first", subclass_reflected_first),
        ("subclass reflected NotImplemented then forward", subclass_notimpl_then_forward),
        ("builtin numeric lhs reaches user __radd__", builtin_numeric_reflected),
        ("builtin sequence lhs reaches user __radd__", builtin_sequence_reflected),
        ("sequence concat follows reflected NotImplemented", builtin_sequence_fallback),
        ("str formatting exception suppresses __rmod__", str_mod_stops_before_reflected),
        ("custom modulo NotImplemented reaches __rmod__", custom_mod_falls_through),
    ]
    for name, scenario in scenarios:
        run(name, scenario)
    return rows


def trace_format_scenarios() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []

    def run(name: str, thunk: Callable[[list[str]], object]) -> None:
        events: list[str] = []
        try:
            result = thunk(events)
            outcome = {
                "kind": "return",
                "class": type(result).__name__,
                "value": clipped_repr(result),
            }
        except BaseException as exc:
            outcome = {
                "kind": "raise",
                "class": type(exc).__name__,
                "message": str(exc),
            }
        rows.append({"name": name, "events": events, "outcome": outcome})

    def string_conversion(events: list[str]) -> object:
        class Value:
            def __str__(self) -> str:
                events.append("Value.__str__")
                return "converted"

        return "%s" % Value()

    def string_conversion_raises(events: list[str]) -> object:
        class Value:
            def __str__(self) -> str:
                events.append("Value.__str__")
                raise RuntimeError("str failed")

        return "%s" % Value()

    def repr_conversion_raises(events: list[str]) -> object:
        class Value:
            def __repr__(self) -> str:
                events.append("Value.__repr__")
                raise LookupError("repr failed")

        return "%r" % Value()

    def float_conversion(events: list[str]) -> object:
        class Value:
            def __float__(self) -> float:
                events.append("Value.__float__")
                return 1.5

        return "%f" % Value()

    def index_conversion(events: list[str]) -> object:
        class Value:
            def __index__(self) -> int:
                events.append("Value.__index__")
                return 15

        return "%x" % Value()

    def mapping_lookup(events: list[str]) -> object:
        class Mapping:
            def __getitem__(self, key: object) -> object:
                events.append(f"Mapping.__getitem__({key!r})")
                return "mapped"

        return "%(x)s" % Mapping()

    def mapping_lookup_raises(events: list[str]) -> object:
        class Mapping:
            def __getitem__(self, key: object) -> object:
                events.append(f"Mapping.__getitem__({key!r})")
                raise OSError("lookup failed")

        return "%(x)s" % Mapping()

    scenarios = [
        ("%s invokes __str__", string_conversion),
        ("%s propagates __str__ exception", string_conversion_raises),
        ("%r propagates __repr__ exception", repr_conversion_raises),
        ("%f invokes __float__", float_conversion),
        ("%x invokes __index__", index_conversion),
        ("mapping format invokes __getitem__", mapping_lookup),
        ("mapping format propagates lookup exception", mapping_lookup_raises),
    ]
    for name, scenario in scenarios:
        run(name, scenario)
    return rows


def mine(include_full: bool) -> dict[str, Any]:
    grouped: dict[tuple[str, str, str], dict[str, Any]] = {}
    full: list[dict[str, Any]] = []

    for op_name, symbol, op in OPERATORS:
        for left in SAMPLES:
            for right in SAMPLES:
                outcome = observe(op, left, right)
                key = (op_name, left.tag, right.tag)
                cell = grouped.setdefault(
                    key,
                    {
                        "operator": op_name,
                        "symbol": symbol,
                        "left_tag": left.tag,
                        "right_tag": right.tag,
                        "outcomes": defaultdict(list),
                    },
                )
                examples = cell["outcomes"][outcome_key(outcome)]
                if len(examples) < 5:
                    examples.append(
                        {
                            "left": left.label,
                            "right": right.label,
                            **outcome,
                        }
                    )
                if include_full:
                    full.append(
                        {
                            "operator": op_name,
                            "symbol": symbol,
                            "left_tag": left.tag,
                            "left": left.label,
                            "right_tag": right.tag,
                            "right": right.label,
                            **outcome,
                        }
                    )

    cells = []
    for cell in grouped.values():
        cell["outcomes"] = dict(sorted(cell["outcomes"].items()))
        cell["value_sensitive"] = len(cell["outcomes"]) > 1
        cells.append(cell)
    cells.sort(key=lambda c: (c["operator"], c["left_tag"], c["right_tag"]))

    report: dict[str, Any] = {
        "implementation": platform.python_implementation(),
        "version": platform.python_version(),
        "version_info": list(sys.version_info[:3]),
        "sample_count": len(SAMPLES),
        "operator_count": len(OPERATORS),
        "concrete_run_count": len(SAMPLES) * len(SAMPLES) * len(OPERATORS),
        "cells": cells,
        "protocol_scenarios": trace_protocol_scenarios(),
        "format_scenarios": trace_format_scenarios(),
    }
    if include_full:
        report["full"] = full
    return report


def stable_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def semantic_row(row: dict[str, Any]) -> list[str]:
    result_class = row["class"]
    # Python 3.14 renamed the concrete class of ``int | None`` from
    # UnionType to Union. Both are the same Pylate runtime category.
    if row["kind"] == "return" and result_class in ("UnionType", "Union"):
        result_class = "type_union"
    return [
        row["operator"],
        row["left_tag"],
        row["left"],
        row["right_tag"],
        row["right"],
        row["kind"],
        result_class,
    ]


def projected_scenario(row: dict[str, Any]) -> dict[str, Any]:
    outcome = row["outcome"]
    projected = {
        "name": row["name"],
        "events": row["events"],
        "outcome": {
            "kind": outcome["kind"],
            "class": outcome["class"],
        },
    }
    if outcome["kind"] == "return":
        projected["outcome"]["value"] = outcome["value"]
    return projected


def regression_projection(report: dict[str, Any]) -> dict[str, Any]:
    rows = [semantic_row(row) for row in report["full"]]
    by_operator: dict[str, list[list[str]]] = defaultdict(list)
    for row in rows:
        by_operator[row[0]].append(row)

    nontrivial = {}
    value_sensitive = {}
    for cell in report["cells"]:
        key = "|".join(
            [cell["operator"], cell["left_tag"], cell["right_tag"]]
        )
        outcomes = sorted(
            "return:type_union"
            if outcome in ("return:UnionType", "return:Union")
            else outcome
            for outcome in cell["outcomes"]
        )
        if outcomes != ["raise:TypeError"]:
            nontrivial[key] = outcomes
        if cell["value_sensitive"]:
            value_sensitive[key] = outcomes

    return {
        "schema": 1,
        "sample_count": report["sample_count"],
        "operator_count": report["operator_count"],
        "concrete_run_count": report["concrete_run_count"],
        "semantic_sha256": hashlib.sha256(
            stable_json(rows).encode("utf-8")
        ).hexdigest(),
        "operator_sha256": {
            op: hashlib.sha256(stable_json(op_rows).encode("utf-8")).hexdigest()
            for op, op_rows in sorted(by_operator.items())
        },
        "nontrivial_cells": nontrivial,
        "value_sensitive_cells": value_sensitive,
        "protocol_scenarios": [
            projected_scenario(row) for row in report["protocol_scenarios"]
        ],
        "format_scenarios": [
            projected_scenario(row) for row in report["format_scenarios"]
        ],
    }


def regression_check(path: str, write: bool) -> None:
    projection = regression_projection(mine(include_full=True))
    if write:
        with open(path, "w") as stream:
            json.dump(projection, stream, indent=2, sort_keys=True)
            stream.write("\n")
        print(
            f"wrote {projection['concrete_run_count']} binary observations "
            f"to {path}"
        )
        return

    with open(path) as stream:
        expected = json.load(stream)
    if projection != expected:
        print("CPython binary semantics drift", file=sys.stderr)
        for key in (
            "sample_count",
            "operator_count",
            "concrete_run_count",
            "semantic_sha256",
            "operator_sha256",
            "nontrivial_cells",
            "value_sensitive_cells",
            "protocol_scenarios",
            "format_scenarios",
        ):
            if projection.get(key) != expected.get(key):
                print(f"  changed: {key}", file=sys.stderr)
        raise SystemExit(1)
    print(
        f"CPython {platform.python_version()}: "
        f"{projection['concrete_run_count']} binary observations match"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--full",
        action="store_true",
        help="include every concrete run, not only grouped outcomes",
    )
    parser.add_argument(
        "--value-sensitive-only",
        action="store_true",
        help="omit cells with a single observed outcome",
    )
    parser.add_argument(
        "--check-regression",
        metavar="FILE",
        help="compare all outcome classes and protocol traces with FILE",
    )
    parser.add_argument(
        "--write-regression",
        metavar="FILE",
        help="write a compact regression projection to FILE",
    )
    args = parser.parse_args()

    if args.check_regression or args.write_regression:
        path = args.check_regression or args.write_regression
        regression_check(os.path.abspath(path), bool(args.write_regression))
        return

    report = mine(args.full)
    if args.value_sensitive_only:
        report["cells"] = [c for c in report["cells"] if c["value_sensitive"]]
    json.dump(report, sys.stdout, indent=2, sort_keys=False)
    print()


if __name__ == "__main__":
    main()

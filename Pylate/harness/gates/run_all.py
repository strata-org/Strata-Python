"""Regression driver for the test suite in this folder.

Per FILE.py: dump the AST (this interpreter; use 3.12+ so match and PEP
695 files parse), run the Lean checker+analyzer, render FILE.html, and
add a row to index.html. Rejection is a result; only a stage that fails
to run aborts.

    python3 run_all.py               # run everything, write index.html
    python3 run_all.py --check       # also diff against expected.json,
                                     # exit 1 on drift
    python3 run_all.py --bless       # rewrite expected.json from this run
    python3 run_all.py FILE.py ...   # subset (no index, no check)
    python3 run_all.py --coverage    # diff coverage_manifest.json against
                                     # the golden logs, exit 1 on gaps

Every accepted program is analyzed under ALL abort-policy presets
(strict, eafp, audit): FILE.<mode>.log.json and FILE.<mode>.html per
mode, so the modes are comparable side by side. Rejection precedes the
analysis, so rejected files run once. expected.json pins, per file,
the rejection digest (status plus sorted rule multiset) or a per-mode
map of acceptance digests (sites, devirt, deferred, policy, aborts).
index.html is fully self-contained: the summary table AND every
rendered section for every mode are embedded in the one page, so it
can be hosted as a single file. Residual details drift legitimately
during development; the pinned digest is the admission-and-shape
contract, and the logs hold the full fixpoints when a diff needs
inspection.
"""
import ast
import concurrent.futures
import difflib
import glob
import json
import os
import platform
import subprocess
import sys
import time

import sys as _sys, os as _os
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
import paths
paths.on_path()

#: The corpus is a sibling of the harness now, so `HERE` is where the programs
#: are, not where this file is. Every generated artifact still lands beside its
#: source, which is what keeps `expected.json`'s keys stable.
HERE = paths.CORPUS
ROOT = paths.PACKAGE
import render_log  # noqa: E402  (CSS, LEGEND, render_section)

MODES = ["strict", "eafp", "audit"]
LEAN = paths.PYLATE
EXPECTED = paths.data("expected.json")
CPYTHON_BINOP_PROBE = os.path.join(paths.PROBES, "cpython_binop_probe.py")
CPYTHON_BINOP_EXPECTED = paths.data("cpython_binop_expected.json")
CPYTHON_RESOLUTION_PROBE = os.path.join(
    paths.PROBES, "cpython_resolution_probe.py"
)


def render_page(title, sections):
    return ("<!doctype html><html lang='en'><head><meta charset='utf-8'>"
            "<meta name='viewport' content='width=device-width,"
            f"initial-scale=1'><title>{title}</title>"
            f"<style>{render_log.CSS}</style></head><body>"
            "<div class='wrap'><p class='eyebrow'>pylate</p>"
            f"<h1>{title}</h1>" + render_log.LEGEND
            + "\n".join(sections) + "</div></body></html>")


def digest(log):
    if log["status"] == "rejected":
        return {"status": "rejected",
                "rules": sorted(v["rule"] for v in log["violations"])}
    s = log["summary"]
    aborts = sum(1 for o in log["obligations"]
                 if o["kind"].startswith("abort:"))
    return {"status": "accepted", "sites": s["sites"],
            "devirt": s["devirt"], "deferred": s["deferred"],
            "policy": log.get("policy", {}).get("preset", ""),
            "aborts": aborts}


def test_name(path):
    return os.path.relpath(path, HERE).replace(os.sep, "/")


def is_test_source(path):
    """Is this a corpus program to analyse?

    The harness used to live in this directory, so this had to name each of its
    thirteen files to keep them from being analysed as corpus -- and anything
    added and forgotten silently became a test case. The harness is a sibling
    directory now, so only genuine corpus exclusions remain.
    """
    name = os.path.basename(path)
    return (
        # `comp.py` is the precision corpus: 2499 sites, and `comp_precision.py`
        # already checks it against 560 two-sided checkpoints. Analysing it here
        # under three policies as well costs roughly an hour per run and adds no
        # signal the checkpoints do not already carry, so the gate that needs it
        # owns it.
        name != "comp.py"
        # Generator output that is an input to another gate, not a case here.
        and not name.startswith("gen_")
        # Artifacts this driver itself writes beside each source.
        and not name.endswith((".annotated.py", ".checked.py"))
        and "__pycache__" not in path.split(os.sep)
    )


def check_cpython_binop_oracle():
    probe = subprocess.run(
        [
            sys.executable,
            CPYTHON_BINOP_PROBE,
            "--check-regression",
            CPYTHON_BINOP_EXPECTED,
        ],
        capture_output=True,
        text=True,
    )
    if probe.returncode != 0:
        raise SystemExit(
            "CPython binary-operator regression failed: "
            + (probe.stderr.strip() or probe.stdout.strip())
        )
    print(probe.stdout.strip())


def check_cpython_resolution_oracle(name, source_path, log):
    lean_resolution = log.get("resolution", {})
    if not lean_resolution.get("classes"):
        return
    probe = subprocess.run(
        [sys.executable, CPYTHON_RESOLUTION_PROBE, source_path],
        capture_output=True,
        text=True,
        timeout=10,
    )
    if probe.returncode != 0:
        raise SystemExit(
            f"{name}: CPython resolution probe failed: "
            + (probe.stderr.strip() or probe.stdout.strip())
        )
    cpython_output = json.loads(probe.stdout)
    cpython_resolution = cpython_output["resolution"]
    base = os.path.splitext(source_path)[0]
    with open(base + ".resolution.lean.json", "w") as snapshot:
        json.dump(lean_resolution, snapshot, indent=2, sort_keys=True)
    with open(base + ".resolution.cpython.json", "w") as snapshot:
        json.dump(cpython_output, snapshot, indent=2, sort_keys=True)
    if cpython_resolution != lean_resolution:
        expected = json.dumps(
            cpython_resolution, indent=2, sort_keys=True
        ).splitlines()
        actual = json.dumps(
            lean_resolution, indent=2, sort_keys=True
        ).splitlines()
        diff = "\n".join(difflib.unified_diff(
            expected,
            actual,
            fromfile="CPython 3.13",
            tofile="Pylate",
            n=2,
        ))
        raise SystemExit(
            f"{name}: resolved declarations disagree with CPython:\n"
            + "\n".join(diff.splitlines()[:120])
        )


def check_cpython_rejection_oracle(name, source_path):
    if name != "reject_invalid_c3.py":
        return
    probe = subprocess.run(
        [sys.executable, CPYTHON_RESOLUTION_PROBE, source_path],
        capture_output=True,
        text=True,
        timeout=10,
    )
    # Whitespace is collapsed before matching. CPython wraps this message at a
    # different column across versions -- 3.12 emits "method resolution\norder",
    # 3.13 keeps it on one line -- and the oracle is about the *semantics*, which
    # are identical: both raise TypeError for an inconsistent linearization.
    # Matching the raw text made a formatting change look like a semantic one.
    text = " ".join((probe.stderr + probe.stdout).split())
    if probe.returncode == 0 or "method resolution order" not in text:
        raise SystemExit(
            f"{name}: CPython {platform.python_version()} did not confirm the "
            f"C3 rejection"
        )


def check_cell_validity(name, mode, log):
    """Every heap cell an analyzed program leaves must be one its location
    class can hold. `CellSelector.validFor` is checked statically for rule data
    and by the `cell-validity` validator condition; the kernel's own `heapSet`
    does not check it, so this covers the hand-written transfers end to end."""
    bad = log.get("cell_violations") or []
    if bad:
        raise SystemExit(
            f"{name} ({mode}): {len(bad)} cell(s) on a class that cannot hold "
            f"them: {', '.join(sorted(bad)[:5])}"
        )


def check_soundness_regression(name, mode, log):
    if name == "baseline_genexpr_kind.py":
        raw_residuals = log["residuals"]
        rows = (list(raw_residuals.values())
                if isinstance(raw_residuals, dict) else raw_residuals)
        next_rows = [
            row for row in rows
            if row["kind"] == "call" and row["desc"] == "next(..)"
        ]
        if (
            len(next_rows) != 1
            or set(next_rows[0]["result"]["tags"]) != {"int"}
            or next_rows[0]["errors"]
            or any(
                "StopIteration" in obligation["kind"]
                or "StopIteration" in obligation["detail"]
                for obligation in log["obligations"]
            )
        ):
            raise SystemExit(
                f"{name} ({mode}): known-nonempty generator must yield "
                "exactly int without StopIteration"
            )

    if mode != "audit":
        return

    raw_residuals = log["residuals"]
    residuals = (list(raw_residuals.values())
                 if isinstance(raw_residuals, dict) else raw_residuals)

    def find(expr, kind=None):
        return [r for r in residuals
                if r["expr"] == expr and (kind is None or r["kind"] == kind)]

    def tags(row):
        return set(row["result"]["tags"])

    def literals(row):
        return set(row["result"]["string_literals"])

    def calls(desc):
        return [
            row for row in residuals
            if row["kind"] == "call" and row["desc"] == desc
        ]

    def require_call(desc, expected_tags, expected_literals=()):
        rows = calls(desc)
        if len(rows) != 1:
            raise SystemExit(
                f"{name}: expected one {desc} residual, got {len(rows)}"
            )
        row = rows[0]
        if (
            tags(row) != set(expected_tags)
            or literals(row) != set(expected_literals)
            or row["errors"]
        ):
            raise SystemExit(
                f"{name}: {desc} expected tags/literals "
                f"{sorted(expected_tags)}/{sorted(expected_literals)}, got "
                f"{sorted(tags(row))}/{sorted(literals(row))} with "
                f"errors {row['errors']}"
            )

    exact_calls = {
        "baseline_callee_order.py": {
            "method_order(..)": ({"str"}, {"receiver-evaluated"}),
            "generic_order(..)": ({"str"}, {"callee-evaluated"}),
        },
        "baseline_dict_literal_order.py": {
            "build(..)": ({"str"}, {"key-evaluated"}),
        },
        "baseline_assignment_target_order.py": {
            "store(..)": ({"str"}, {"target-evaluated"}),
        },
        "baseline_init_failure.py": {
            "construct(..)": ({"str"}, {"init-evaluated"}),
        },
        "baseline_exception_init.py": {
            "construct_before_raise(..)": (
                {"str"}, {"exception-initialized"}
            ),
        },
        "baseline_try_else_escape.py": {
            "route_else_exception(..)": (
                {"str"}, {"correct-outer-handler"}
            ),
        },
        "baseline_builtin_protocol.py": {
            "length(..)": ({"str"}, {"caught-len-error"}),
            "iteration(..)": ({"str"}, {"caught-iter-error"}),
            "next_item(..)": ({"str"}, {"caught-next-error"}),
        },
        "baseline_comparison_protocol.py": {
            "compare(..)": ({"str"}, {"caught-reflected-error"}),
        },
        "baseline_membership_protocol.py": {
            "contains(..)": ({"str"}, {"caught-contains-error"}),
        },
        "baseline_not_protocol.py": {
            "negate(..)": ({"str"}, {"caught-bool-error"}),
        },
        "baseline_string_protocol.py": {
            "stringify(..)": ({"str"}, {"caught-str-error"}),
            "represent(..)": ({"str"}, {"caught-repr-error"}),
            "default_string_uses_repr(..)": (
                {"str"}, {"caught-default-repr-error"}
            ),
            "bad_string_result(..)": (
                {"str"}, {"caught-bad-str-result"}
            ),
        },
        "baseline_loop_fixpoint.py": {
            "propagate_through_loop(..)": ({"str"}, {"reached"}),
        },
        "baseline_comprehension_fixpoint.py": {
            "propagate_through_comprehension(..)": (
                {"str"}, {"reached"}
            ),
        },
        "baseline_no_backward_flow.py": {
            "no_backward_flow(..)": ({"int"}, set()),
        },
    }
    for desc, (expected_tags, expected_literals) in exact_calls.get(
        name, {}
    ).items():
        require_call(desc, expected_tags, expected_literals)

    forbidden_calls = {
        "baseline_dict_literal_order.py": {"late_value(..)"},
        "baseline_assignment_target_order.py": {"late_index(..)"},
        "baseline_init_failure.py": {"late_step(..)"},
    }
    reached_forbidden = sorted(
        desc for desc in forbidden_calls.get(name, set()) if calls(desc)
    )
    if reached_forbidden:
        raise SystemExit(
            f"{name}: exceptional sequencing reached "
            + ", ".join(reached_forbidden)
        )

    if name == "baseline_exceptional_assignment.py":
        if (
            log["module"]["may_raise"] != ["TypeError"]
            or set(log["lines"]) != {"1", "2"}
        ):
            raise SystemExit(
                f"{name}: a guaranteed-failing RHS must not assign or "
                "reach following statements"
            )
        return

    if name == "baseline_unbound_reads.py":
        obligations = {
            (row["kind"], row["detail"]) for row in log["obligations"]
        }
        required = {
            ("maybe-unbound",
             "read of local_value: unbound on some path"),
            ("definitely-unbound",
             "read of missing_global: no binding reaches this point"),
        }
        if not required <= obligations:
            raise SystemExit(
                f"{name}: missing local/global unbound-read distinctions"
            )
        require_call(
            "catch_global(..)", {"str"}, {"caught-global-error"}
        )
        if "caught-local-error" not in literals(calls("catch_local(..)")[0]):
            raise SystemExit(
                f"{name}: UnboundLocalError does not reach its handler"
            )
        return

    if name == "baseline_nested_annotations.py":
        details = {
            row["detail"] for row in log["obligations"]
            if row["kind"] == "param-annotation"
        }
        expected = {
            "list_head: argument for values must satisfy its annotation",
            "dict_value: argument for values must satisfy its annotation",
            "tuple_second: argument for values must satisfy its annotation",
            "accept_set: argument for values must satisfy its annotation",
        }
        if details != expected:
            raise SystemExit(
                f"{name}: nested parameter checks are incomplete: "
                f"{sorted(details)}"
            )
        return

    if name == "baseline_string_protocol.py":
        handler_rows = [
            row
            for table in log["handlers"].values()
            for row in table["rows"]
        ]
        for method, exception in (
            ("StrBomb.__str__", "LookupError"),
            ("ReprBomb.__repr__", "RuntimeError"),
            ("ReprOnlyBomb.__repr__", "OSError"),
        ):
            if not any(
                method in outcome
                for row in residuals
                for outcome in row["cases"].values()
            ):
                raise SystemExit(f"{name}: did not dispatch through {method}")
            if not any(
                row.get("exc") == exception
                and row.get("caught_by", {}).get("clause") == exception
                for row in handler_rows
            ):
                raise SystemExit(
                    f"{name}: did not propagate {exception} from {method}"
                )
        return

    if name == "ix_except_hierarchy.py":
        handler_rows = [
            row
            for table in log["handlers"].values()
            for row in table["rows"]
        ]
        if not any(
            row.get("exc") == "ConfigError"
            and row.get("caught_by", {}).get("clause") == "AppError"
            for row in handler_rows
        ) or not any(
            row.get("exc") == "SystemExit"
            and row.get("match") == "propagates"
            for row in handler_rows
        ):
            raise SystemExit(
                f"{name}: exception subclass routing is incorrect"
            )
        return

    if name == "pyhard/21_exception_target_lifetime.py":
        for line, targets in (
            ("21", ("caught",)),
            ("33", ("caught", "replacement")),
        ):
            env = log["lines"].get(line, {}).get("env", {})
            for target in targets:
                if set(env.get(target, {}).get("tags", [])) != {"unbound"}:
                    raise SystemExit(
                        f"{name}: handler target {target} is not unbound "
                        f"after cleanup at line {line}"
                    )
        return

    if name == "baseline_no_backward_flow.py":
        before = [
            row for row in residuals
            if row["kind"] == "binop" and row["expr"] == "value + 1"
        ]
        after = [
            row for row in residuals
            if row["kind"] == "binop" and row["expr"] == 'value + "!"'
        ]
        if (
            len(before) != 1
            or tags(before[0]) != {"int"}
            or set(before[0]["cases"]) != {"(int,int)"}
            or before[0]["errors"]
            or len(after) != 1
            or tags(after[0]) != {"str"}
            or set(after[0]["cases"]) != {"(str,str)"}
            or after[0]["errors"]
        ):
            raise SystemExit(
                f"{name}: a later assignment contaminated an earlier "
                "program location"
            )
        return

    if name == "gp_binop_matrix.py":
        source_path = os.path.join(HERE, name)
        with open(source_path, encoding="utf-8") as source_file:
            tree = ast.parse(source_file.read(), source_path)
        by_line = {row["line"]: row for row in residuals}
        runtime_tags = {
            type(None): "none",
            bool: "bool",
            int: "int",
            float: "float",
            str: "str",
            list: "list",
            tuple: "tuple",
            set: "set",
            dict: "dict",
        }
        failures = []
        statements = sorted(
            (
                node for node in ast.walk(tree)
                if isinstance(node, ast.Assign)
                and isinstance(node.value, ast.BinOp)
            ),
            key=lambda node: node.lineno,
        )
        for statement in statements:
            expression = ast.Expression(statement.value)
            row = by_line.get(statement.lineno)
            if row is None:
                failures.append(
                    f"line {statement.lineno}: missing residual"
                )
                continue
            try:
                value = eval(
                    compile(expression, source_path, "eval"), {}
                )
            except BaseException as error:
                if not any(
                    type(error).__name__ in text
                    for text in row["errors"]
                ):
                    failures.append(
                        f"line {statement.lineno}: missing "
                        f"{type(error).__name__}"
                    )
            else:
                expected = runtime_tags[type(value)]
                if expected not in tags(row):
                    failures.append(
                        f"line {statement.lineno}: missing {expected}"
                    )
        if failures:
            raise SystemExit(
                f"{name}: CPython matrix regression failed: "
                + "; ".join(failures[:20])
            )
        return

    if name == "binary_dispatch_soundness.py":
        failures = []

        def require(expr, expected_tags=(), errors=(), case=None,
                    forbidden_case=None, forbidden_tags=(),
                    forbidden_errors=()):
            rows = find(expr, "binop")
            if not rows:
                failures.append(f"{expr}: expected a binary residual")
                return
            actual_tags = set().union(*(tags(row) for row in rows))
            if not set(expected_tags) <= actual_tags:
                failures.append(
                    f"{expr}: expected tags {sorted(expected_tags)}, "
                    f"got {sorted(actual_tags)}"
                )
            if set(forbidden_tags) & actual_tags:
                failures.append(
                    f"{expr}: forbidden tags "
                    f"{sorted(set(forbidden_tags) & actual_tags)}"
                )
            error_text = " ".join(
                error for row in rows for error in row["errors"]
            )
            for error in errors:
                if error not in error_text:
                    failures.append(f"{expr}: missing {error}")
            for error in forbidden_errors:
                if error in error_text:
                    failures.append(f"{expr}: unexpectedly has {error}")
            case_text = " ".join(
                case for row in rows for case in row["cases"].values()
            )
            if case and case not in case_text:
                failures.append(f"{expr}: missing case {case}")
            if forbidden_case and forbidden_case in case_text:
                failures.append(f"{expr}: unexpectedly reached {forbidden_case}")

        require("1 + ReflectedAdd()", ["int"], case="ReflectedAdd.__radd__")
        require("[1] + ReflectedAdd()", ["int"],
                case="ReflectedAdd.__radd__")
        require("[1] + DeclinedAdd()", errors=["TypeError"])
        for expr, method in (
            ("1 - ReflectedOps()", "__rsub__"),
            ("1 * ReflectedOps()", "__rmul__"),
            ("1 / ReflectedOps()", "__rtruediv__"),
            ("1 // ReflectedOps()", "__rfloordiv__"),
            ("1 % ReflectedOps()", "__rmod__"),
            ("1 ** ReflectedOps()", "__rpow__"),
            ("1 << ReflectedOps()", "__rlshift__"),
            ("1 >> ReflectedOps()", "__rrshift__"),
            ("1 & ReflectedOps()", "__rand__"),
            ("1 ^ ReflectedOps()", "__rxor__"),
            ("1 | ReflectedOps()", "__ror__"),
        ):
            require(expr, ["int"], case=f"ReflectedOps.{method}")
        require('"ab" % 3', errors=["TypeError"])
        require('"ab" % []', ["str"])
        require('"%s" % 3', ["str"])
        require('"%d" % "x"', errors=["TypeError"])
        require('"plain" % ModTrap()', errors=["TypeError"],
                forbidden_case="ModTrap.__rmod__")
        require('"%s" % StrRaises()', errors=["RuntimeError"],
                forbidden_tags=["str"])
        require('"%r" % ReprRaises()', errors=["LookupError"],
                forbidden_tags=["str"])
        require('"%(key)s" % MappingRaises()', errors=["OSError"],
                forbidden_tags=["str"])
        require(
            '"%(key)s" % MappingReturnsRaisingValue()',
            errors=["RuntimeError"],
            forbidden_tags=["str"],
        )
        require('"%d" % value', ["str"],
                errors=["ValueError", "OverflowError"])
        require('"%d" % IntPreferred()', ["str"],
                forbidden_errors=["LookupError"])
        require("fmt % AlternativeFormat()", ["str"],
                errors=["RuntimeError"])
        unary = find("-Negates()", "unary")
        if not unary or "str" not in tags(unary[0]):
            failures.append("-Negates(): missing str result")
        unary_raise = find("-NegRaises()", "unary")
        if (not unary_raise
                or not any("ArithmeticError" in error
                           for error in unary_raise[0]["errors"])
                or tags(unary_raise[0])):
            failures.append("-NegRaises(): expected exception-only result")
        narrowed_int = find("value + 1", "binop")
        if (not narrowed_int
                or tags(narrowed_int[0]) != {"int"}
                or set(narrowed_int[0]["cases"])
                != {"(bool,int)", "(int,int)"}):
            failures.append(
                "isinstance(value, int): expected exactly bool|int cases"
            )
        narrowed_complex = find("-value", "unary")
        if (not narrowed_complex
                or tags(narrowed_complex[0]) != {"complex"}
                or set(narrowed_complex[0]["cases"]) != {"complex"}):
            failures.append(
                "isinstance(value, complex): expected exactly complex"
            )
        require("ForwardWins() + ReflectedLoses()", ["int"],
                case="ForwardWins.__add__",
                forbidden_case="ReflectedLoses.__radd__")
        require("ForwardRaises() + ReflectedUnreachable()",
                errors=["LookupError"],
                forbidden_case="ReflectedUnreachable.__radd__")
        require("SameType() + SameType()", errors=["TypeError"],
                forbidden_case="SameType.__radd__")
        require("(1) + (\"x\")", ["tuple"])
        require("(1) * 2", ["tuple"])
        require("2 * (1)", ["tuple"])
        require("[1] * 2", ["list"], errors=["OverflowError"])
        require('"x" * Indexed()', ["str"], case="Indexed.__index__")
        require("Indexed() * [1]", ["list"], case="Indexed.__index__")
        require("1 << 2", ["int"], errors=["OverflowError"])
        require("{1, 2} - {2}", ["set"])
        require("{1, 2} & {2}", ["set"])
        require("{1, 2} ^ {2, 3}", ["set"])
        require("{1, 2} | {2, 3}", ["set"])
        require('{"a": 1} | {"b": "x"}', ["dict"])
        require('keys & ["a"]', ["set"])
        require('items | {("b", 2)}', ["set"])
        require("values | {1}", errors=["TypeError"])
        require("keys & ViewReflectedTrap()", errors=["TypeError"],
                forbidden_case="ViewReflectedTrap.__rand__")
        require("values & ViewReflectedTrap()", ["int"],
                case="ViewReflectedTrap.__rand__")
        require("{1} | ReflectedOps()", ["int"],
                case="ReflectedOps.__ror__")
        require('{"a": 1} | ReflectedOps()', ["int"],
                case="ReflectedOps.__ror__")
        require("TypeA | TypeA", ["type"])
        require("TypeA | TypeB", ["type_union"])
        require("TypeA | None", ["type_union"])
        require("TypeA | TypeB | None", ["type_union"])
        require("left ** right", ["float", "complex"],
                errors=["ZeroDivisionError", "OverflowError"])
        if failures:
            raise SystemExit(
                f"{name}: binary dispatch regression failed: "
                + "; ".join(failures)
            )
        return

    if name == "binary_protocol_effect_state.py":
        reads = find("box.value", "getattr")
        expected_literals = {
            "iterated", "indexed", "exhausted", "failed",
        }
        actual_literals = set().union(*(literals(row) for row in reads))
        if (
            len(reads) != 4
            or any(tags(row) != {"str"} for row in reads)
            or actual_literals != expected_literals
        ):
            raise SystemExit(
                f"{name}: continuations must see exactly the post-hook "
                f"heap states, got {sorted(actual_literals)}"
            )
        protocol_rows = [
            row for row in residuals
            if row["kind"] == "binop" and row["desc"] == "binop BitAnd"
        ]
        routes = " ".join(
            outcome
            for row in protocol_rows
            for outcome in row["cases"].values()
        )
        errors = " ".join(
            error for row in protocol_rows for error in row["errors"]
        )
        if (
            "IterMutator.__iter__" not in routes
            or "GetItemMutator.__getitem__" not in routes
            or "TypeError" not in errors
        ):
            raise SystemExit(
                f"{name}: protocol-hook TypeError routes are incomplete"
            )
        return

    if name != "soundness_heap_dispatch.py":
        return

    failures = []
    attr = find("a.x", "getattr")
    if not attr or not {"int", "str"} <= tags(attr[0]):
        failures.append("ambiguous object store lost int or str")
    add = find("a.x + 1", "binop")
    if (not add or "int" not in tags(add[0])
            or not any("TypeError" in e for e in add[0]["errors"])):
        failures.append("object-store continuation lost int or TypeError")
    for row in find("a.get(..)", "call"):
        if not {"int", "none"} <= tags(row):
            failures.append(f"line {row['line']}: TypedDict mutation lost old/present state")
    if len(find("a.get(..)", "call")) != 3:
        failures.append("expected clear/update/setdefault result sites")
    copied = find("copied.get(..)", "call")
    if not copied or not {"str", "none"} <= tags(copied[0]):
        failures.append("TypedDict copy lost a source shape")
    primitive = find("value.extra =", "setattr")
    if (not primitive
            or not any("AttributeError" in e for e in primitive[0]["errors"])):
        failures.append("primitive attribute store lost AttributeError")
    if not any(o["kind"] == "type-error"
               and "LeftCell.left" in o["detail"]
               for o in log["obligations"]):
        failures.append("TypedDict mapping update lost field-type obligation")
    if failures:
        raise SystemExit(f"{name}: soundness regression failed: "
                         + "; ".join(failures))


def took(started):
    """` (12.4s)` for a file slow enough to be worth noticing, else empty."""
    seconds = time.monotonic() - started
    return f" ({seconds:.1f}s)" if seconds >= 2.0 else ""


def run(path):
    file_started = time.monotonic()
    base = os.path.splitext(path)[0]
    name = test_name(path)
    # The analyzer's input: the Strata AST, produced by the repo's
    # `py_to_strata` and read back through `StrataDDM.Program.fromIon`.
    try:
        ast_p = paths.make_analyzer_input(path, base)
    except SyntaxError as error:
        raise SystemExit(f"{name}: parse failed (need Python 3.12+ for "
                         f"match/PEP695 files): {error}")
    except subprocess.CalledProcessError as error:
        detail = (error.stderr or b"").decode(errors="replace").strip()
        raise SystemExit(f"{name}: building the analyzer input failed: {detail}")
    # One invocation for all three policies. Roughly 30ms of each run is the
    # engine constructing its rule tables at module init, against about 5ms of
    # analysis for a small file, so three separate invocations paid that three
    # times. `--emit` parses and lowers once and runs each policy in its own
    # fresh context.
    emits = []
    for mode in MODES:
        emits += ["--emit", f"{mode}={base}.{mode}.log.json"]
    lean = subprocess.run([LEAN, ast_p, "--src", path, *emits],
                          capture_output=True, text=True)
    if lean.returncode != 0:
        raise SystemExit(f"{name}: pylate failed: {lean.stderr.strip()}")
    per_mode = {}
    resolution_log = None
    for mode in MODES:
        log_p = f"{base}.{mode}.log.json"
        html_p = f"{base}.{mode}.html"
        with open(log_p) as f:
            log = json.load(f)
        check_cell_validity(name, mode, log)
        check_soundness_regression(name, mode, log)
        with open(html_p, "w") as f:
            f.write(render_page(f"{name} ({mode})",
                                [render_log.render_section(log)]))
        d = digest(log)
        if d["status"] == "rejected":
            # rejection precedes the analysis: one run tells all
            check_cpython_rejection_oracle(name, path)
            return name, d, (f"{name}: rejected ({len(d['rules'])} "
                             f"violations: "
                             f"{', '.join(sorted(set(d['rules'])))})"
                             f"{took(file_started)}")
        if resolution_log is None:
            resolution_log = log
        per_mode[mode] = d
    check_cpython_resolution_oracle(name, path, resolution_log)
    ds = per_mode["strict"]
    return name, per_mode, (
        f"{name}: accepted (sites {ds['sites']}, devirt {ds['devirt']}, "
        f"deferred {ds['deferred']}; aborts "
        + "/".join(str(per_mode[m]["aborts"]) for m in MODES)
        + " under " + "/".join(MODES) + ")" + took(file_started))


#: Set by `main` before each file so `run`'s report line can carry the counter
#: without threading it through every helper. A module-level cell rather than a
#: parameter because `run` is also called directly for a single explicit file,
#: where there is no meaningful total.
_PROGRESS = {"index": 0, "total": 0, "started": None}


def set_progress(index, total, started):
    _PROGRESS.update(index=index, total=total, started=started)


def progress_prefix():
    """`[ 12/229  0:04:31]`, or empty when running one explicit file."""
    if not _PROGRESS["total"]:
        return ""
    elapsed = int(time.monotonic() - _PROGRESS["started"])
    width = len(str(_PROGRESS["total"]))
    return (f"[{_PROGRESS['index']:>{width}}/{_PROGRESS['total']} "
            f"{elapsed // 3600}:{elapsed // 60 % 60:02d}:{elapsed % 60:02d}] ")


def run_all_files(files):
    """Analyse every file, in parallel when there is more than one.

    Each file writes only its own artifacts and reads only its own source, so
    the work is independent and a process pool is safe. One worker per core, but
    never more workers than files. A single file stays in-process, so an explicit
    one-file run keeps its traceback and does not pay pool startup.
    """
    total = len(files)
    started = time.monotonic()
    results = {}
    if total == 1:
        set_progress(1, 1, started)
        name, digest_or_status, message = run(files[0])
        print(progress_prefix() + message)
        return {name: digest_or_status}
    workers = min(total, os.cpu_count() or 1)
    # Longest first. Each task now analyses all three policies in one process, so
    # tasks are ~3x longer and a big file submitted late becomes a straggler that
    # nothing overlaps with -- which cost more wall clock than the saved startups
    # gained. Source size is a good enough proxy for cost.
    ordered = sorted(files, key=lambda p: -os.path.getsize(p))
    with concurrent.futures.ProcessPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(run, path): path for path in ordered}
        for index, future in enumerate(
                concurrent.futures.as_completed(futures), 1):
            # The counter follows completion order, which is not source order:
            # the point is liveness, and `--check` compares a dict.
            set_progress(index, total, started)
            name, digest_or_status, message = future.result()
            results[name] = digest_or_status
            print(progress_prefix() + message)
    return results


def write_index(results, drift):
    """A real index: one row per program, linking out to the per-mode pages.

    It used to embed every rendered section for every mode, which made a single
    30 MB page that no browser opens comfortably. The standalone
    `FILE.<mode>.html` pages were already being written beside it, so the
    embedding was a second copy of all of them.
    """
    rows = []
    for name, d in sorted(results.items()):
        base = os.path.splitext(name)[0]
        if "status" in d:  # rejected
            badge = "<span class='badge rej'>rejected</span>"
            detail = ", ".join(sorted(set(d["rules"])))
            cells = f"<td colspan='{len(MODES)}'>{detail}</td>"
            # A rejected program is analysed once; its page carries the
            # violations.
            link = f"{base}.strict.html"
        else:
            badge = "<span class='badge acc'>accepted</span>"
            cells = ""
            link = f"{base}.{MODES[0]}.html"
            for mode in MODES:
                dm = d[mode]
                cells += (f"<td><a href='{base}.{mode}.html'>{mode}</a>: "
                          f"{dm['sites']} sites, {dm['aborts']} aborts"
                          + (f", {dm['deferred']} deferred"
                             if dm['deferred'] else "") + "</td>")
        dr = drift.get(name, "")
        drcell = f"<td class='drift'>{dr}</td>" if drift else ""
        rows.append(f"<tr><td><a href='{link}'>{name}</a></td>"
                    f"<td>{badge}</td>{cells}{drcell}</tr>")
    drhead = "<th>drift</th>" if drift else ""
    status = ""
    if drift:
        bad = sum(1 for v in drift.values() if v)
        status = (f"<p class='fail'>DRIFT in {bad} files</p>" if bad
                  else "<p class='pass'>all files match expected.json</p>")
    mode_heads = "".join(f"<th>{m}</th>" for m in MODES)
    table_css = """
table.idx{border-collapse:collapse;width:100%;font-size:12.5px;
  background:var(--card)}
table.idx th,table.idx td{border:1px solid var(--line);padding:3px 8px;
  text-align:left}
table.idx th{background:var(--page)}
.badge{font-size:11px;font-weight:600;border-radius:4px;padding:1px 6px}
.acc{color:var(--devirt);background:var(--devirt-bg)}
.rej{color:var(--error);background:var(--error-bg)}
.pass{color:var(--devirt);font-weight:600}
.fail{color:var(--error);font-weight:600}
.drift{color:var(--error);font-family:var(--mono);font-size:12px}
"""
    intro = (f"<p class='stats'>{len(results)} programs, every accepted "
             "one analyzed under all abort-policy presets "
             f"({', '.join(MODES)}). Each cell links to that program's page "
             "for that policy, which carries the per-line abstract states. "
             "Regenerate with <code>python3 gates.py --fast</code>; "
             "regression-check with <code>run_all.py --check</code>; repin "
             "with <code>--bless</code>; coverage-check with "
             "<code>--coverage</code>.</p>"
             + status)
    table = (f"<table class='idx'><thead><tr><th>program</th>"
             f"<th>admission</th>{mode_heads}{drhead}</tr></thead>"
             f"<tbody>{''.join(rows)}</tbody></table>")
    page = ("<!doctype html><html lang='en'><head><meta charset='utf-8'>"
            "<meta name='viewport' content='width=device-width,"
            "initial-scale=1'><title>pylate test suite</title>"
            f"<style>{render_log.CSS}{table_css}</style></head><body>"
            "<div class='wrap'><p class='eyebrow'>pylate</p>"
            "<h1>pylate test suite</h1>" + intro + table
            + render_log.LEGEND
            + "</div></body></html>")
    with open(os.path.join(HERE, "index.html"), "w") as f:
        f.write(page)


def main():
    # Python block-buffers stdout when it is not a tty, so piping this to a file
    # held every per-file line until exit and a long run looked like a hang.
    try:
        sys.stdout.reconfigure(line_buffering=True)
    except AttributeError:  # pragma: no cover - Python < 3.7
        pass
    args = [a for a in sys.argv[1:]]
    check = "--check" in args
    bless = "--bless" in args
    if "--coverage" in args:
        import coverage
        coverage.coverage()
        return
    args = [a for a in args if a not in ("--check", "--bless")]
    explicit = bool(args)
    if not explicit:
        check_cpython_binop_oracle()
        for stale in glob.glob(os.path.join(HERE, "**", "*.log.json"),
                               recursive=True) + \
                glob.glob(os.path.join(HERE, "**", "*.html"),
                          recursive=True) + \
                glob.glob(
                    os.path.join(HERE, "**", "*.resolution.*.json"),
                    recursive=True,
                ):
            os.remove(stale)
    files = args or sorted(
        p for p in glob.glob(os.path.join(HERE, "**", "*.py"),
                             recursive=True)
        if is_test_source(p))
    results = run_all_files(files)
    if explicit:
        return
    drift = {}
    if check or bless:
        if bless:
            with open(EXPECTED, "w") as f:
                json.dump(results, f, indent=1, sort_keys=True)
            print(f"\nblessed {len(results)} entries into expected.json")
        else:
            with open(EXPECTED) as f:
                exp = json.load(f)
            for name in sorted(set(exp) | set(results)):
                if name not in results:
                    drift[name] = "missing from run"
                elif name not in exp:
                    drift[name] = "not in expected.json"
                elif exp[name] != results[name]:
                    drift[name] = f"expected {exp[name]}, got {results[name]}"
                else:
                    drift[name] = ""
    write_index(results, drift if check else {})
    if check:
        bad = {k: v for k, v in drift.items() if v}
        if bad:
            print(f"\nDRIFT ({len(bad)}):")
            for k, v in sorted(bad.items()):
                print(f"  {k}: {v}")
            sys.exit(1)
        print(f"\nOK: {len(results)} files match expected.json")


if __name__ == "__main__":
    main()

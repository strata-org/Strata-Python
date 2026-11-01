"""Write PyLate's scenarios as Python programs, one file per scenario, for the differential
runner.

    python3 pylate_programs.py OUTDIR

It reads PyLate's callable-rule scenarios (`Pylate/harness/data/callable_rule_scenarios.json`
and `callable_rule_fuzz.json`), its rule-validity cases (`rule_validity_cases.json`) and the
dispatch-order scenarios of `Pylate/harness/probes/cpython_binop_probe.py`, and writes
`OUTDIR/<id>.py` for each concrete one. A callable-rule scenario becomes `events = []`, its setup, and `result = <call>`; for a call
that returns a dict view or an iterator, the program also keeps `repr(result)` or
`list(result)`, so that the trace shows the content; for a call that advances an iterator
(`next` and the generator methods), it keeps what is left of the iterator. A rule-validity case is a whole module and
runs as it is. A probe scenario becomes its function,
without its annotations, and `result = <name>(events)`. Scenarios without an execution (the abstract ones) are skipped. It
prints the ids in order, one per line.
"""

import ast
import json
import pathlib
import re
import sys
import textwrap

ROOT = pathlib.Path(__file__).resolve().parents[3]
DATA = ROOT / "Pylate" / "harness" / "data"
PROBE = ROOT / "Pylate" / "harness" / "probes" / "cpython_binop_probe.py"

# Rule keys whose result is a dict view, and those whose result is an iterator.
VIEWS = {"dict.keys", "dict.values", "dict.items"}
ITERATORS = {"iter"}
# Rule keys whose call advances an iterator among the roots: the program also keeps what is left
# of it, so that the trace shows the advance.
ADVANCES = {"next", "gen.send", "gen.throw", "gen.close"}


def advanced_root(call):
    """The iterator that a call advances: the first argument of `next(x)`, or the receiver of a
    generator method."""
    m = re.match(r"next\((\w+)", call) or re.match(r"(\w+)\.", call)
    return m.group(1) if m else ""


def callable_programs():
    for name in ("callable_rule_scenarios.json", "callable_rule_fuzz.json"):
        for s in json.loads((DATA / name).read_text())["scenarios"]:
            e = s.get("execution")
            if not e:
                continue
            lines = ["events = []", e["setup"], f"result = {e['call']}"]
            if s["rule_key"] in VIEWS:
                lines.append("result_repr = repr(result)")
            elif s["rule_key"] in ITERATORS:
                lines.append("result_items = list(result)")
            if s["rule_key"] in ADVANCES:
                root = advanced_root(e["call"])
                if re.search(rf"^{root} = ", e["setup"], re.M):
                    lines.append(f"{root}_rest = list({root})")
            yield s["id"], "\n".join(lines) + "\n"


def validity_programs():
    for c in json.loads((DATA / "rule_validity_cases.json").read_text())["cases"]:
        rule = re.sub(r"[^A-Za-z0-9]+", "_", c["rule"]).strip("_")
        yield f"validity_{rule}_{c['name']}", c["source"]


def drop_annotations(fn):
    """`fn` without its annotations, which the probe uses only for type checking: evaluating
    `list[str]` would only test `types.GenericAlias`, not the dispatch order."""
    for node in ast.walk(fn):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            node.returns = None
        elif isinstance(node, ast.arg):
            node.annotation = None
    return fn


def probe_programs():
    tree = ast.parse(PROBE.read_text())
    for fn in tree.body:
        if not (isinstance(fn, ast.FunctionDef)
                and fn.name in ("trace_protocol_scenarios", "trace_format_scenarios")):
            continue
        kind = fn.name.removeprefix("trace_").removesuffix("_scenarios")
        for inner in fn.body:
            if isinstance(inner, ast.FunctionDef) and inner.name != "run":
                body = ast.unparse(drop_annotations(inner))
                yield (f"probe_{kind}_{inner.name}",
                       f"events = []\n{body}\nresult = {inner.name}(events)\n")


def main(out):
    out = pathlib.Path(out)
    out.mkdir(parents=True, exist_ok=True)
    seen = set()
    for pid, text in [*callable_programs(), *validity_programs(), *probe_programs()]:
        assert pid not in seen, f"duplicate id {pid}"
        seen.add(pid)
        (out / f"{pid}.py").write_text(text)
        print(pid)


if __name__ == "__main__":
    main(sys.argv[1])

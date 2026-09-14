"""Coverage ledger: diff coverage_manifest.json against what the golden
logs actually exercise. Separate unit from the runner so the manifest
contract can evolve on its own; run via `run_all.py --coverage` or
directly: `python3 coverage.py`.

One entry was *retired* rather than left uncovered: the violation site
`unsupported-node / statement node`. That was the runtime catch-all at the end of
`lowerStmt`'s dispatch, reachable when the lowering met a statement kind it did
not recognise. Since the front end moved to the Strata AST the match is over the
28 `stmt` constructors and the compiler checks it is total, so every statement is
either lowered or rejected by a rule of its own and there is no longer a runtime
path to cover. The guarantee moved from a test to the type system; it was not
dropped.
"""
import glob
import json
import os
import sys

import sys as _sys, os as _os
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
import paths
paths.on_path()
HERE = paths.CORPUS


def coverage():
    """Diff the coverage manifest against what the golden logs actually
    exercise. Reads *.log.json from disk (run the suite first). Exit 1
    on any uncovered entry: coverage is a failing check, not an opinion.
    """
    with open(paths.data("coverage_manifest.json")) as f:
        man = json.load(f)
    viols, cases, errors, obligs, kinds = set(), set(), set(), set(), set()
    # Recursive: the corpus is grouped into role directories, so a flat glob at
    # its root finds nothing and every manifest cell reads as uncovered.
    for p in sorted(glob.glob(os.path.join(HERE, "**", "*.log.json"),
                              recursive=True)):
        with open(p) as f:
            log = json.load(f)
        for v in log.get("violations", []):
            viols.add((v["rule"], v["detail"]))
        for r in log.get("residuals", {}).values():
            for t, o in r["cases"].items():
                cases.add((r["kind"], r["desc"], t, o))
            for e in r["errors"]:
                errors.add((r["kind"], r["desc"], e))
        for o in log.get("obligations", []):
            obligs.add(o["kind"])
        for d in log.get("dispatch", []):
            kinds.add(d["target"]["kind"])
    missing = []
    for rule, marker in man["violation_sites"]:
        if not any(r == rule and marker in d for r, d in viols):
            missing.append(f"violation site: {rule} / {marker}")
    for tm in man["modeled_builtins"]:
        if not any(o == f"builtin {tm}" for _, _, _, o in cases):
            missing.append(f"modeled builtin: {tm}")
    for tag in man["threeway_opaque_tags"]:
        if not any(o.startswith(f"builtin {tag}.") and o.endswith("(opaque)")
                   for _, _, _, o in cases):
            missing.append(f"opaque arm: {tag}")
    for tag in man["threeway_absent_tags"]:
        if not any(e.startswith(f"{tag} -> ") and "AttributeError" in e
                   for _, _, e in errors):
            missing.append(f"absent arm: {tag}")
    cat_of = {"TypeError": "dispatch", "AttributeError": "dispatch",
              "NameError": "dispatch", "UnboundLocalError": "dispatch",
              "FrozenInstanceError": "frozen", "KeyError": "key",
              "IndexError": "index", "ZeroDivisionError": "arith",
              "OverflowError": "arith", "ValueError": "value",
              "StopIteration": "exhaustion"}
    hit = {cat_of.get(k.split(":", 1)[1], "?")
           for k in obligs if k.startswith("abort:")}
    for cat in man["abort_categories"]:
        if cat not in hit:
            missing.append(f"abort category: {cat}")
    for k in man["dispatch_kinds"]:
        if k not in kinds:
            missing.append(f"dispatch target kind: {k}")
    for n in man["builtin_calls"]:
        if not any(o == f"builtin {n}" for _, _, _, o in cases):
            missing.append(f"builtin call: {n}")
    for op, lt, rt in man["binop_cells"]:
        pair = f"({lt},{rt})"
        got = any(k == "binop" and d == f"binop {op}" and t == pair
                  for k, d, t, _ in cases) or \
              any(k == "binop" and d == f"binop {op}" and e.startswith(pair)
                  for k, d, e in errors)
        if not got:
            missing.append(f"binop cell: {op} {pair}")
    total = (len(man["violation_sites"]) + len(man["modeled_builtins"])
             + len(man["threeway_opaque_tags"])
             + len(man["threeway_absent_tags"])
             + len(man["abort_categories"]) + len(man["dispatch_kinds"])
             + len(man["builtin_calls"]) + len(man["binop_cells"]))
    print(f"coverage: {total - len(missing)}/{total} manifest entries "
          f"exercised by the golden logs")
    if missing:
        print(f"\nUNCOVERED ({len(missing)}):")
        for m in missing:
            print(f"  {m}")
        sys.exit(1)



if __name__ == "__main__":
    coverage()

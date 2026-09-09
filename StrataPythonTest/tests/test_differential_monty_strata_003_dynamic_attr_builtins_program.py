# Feature: DYNAMIC ATTRIBUTE BUILTINS — getattr / setattr / hasattr (worklist item 3).
#
# Monty result (pydantic-monty 0.0.18, the running oracle):
#   These builtins are SHIPPED (builtins.md lists getattr/hasattr/setattr) but
#   stubbed to ALWAYS-MISS — they never perform real attribute resolution by
#   string name:
#     getattr(d, "get")           -> AttributeError        (even though d.get exists)
#     getattr(d, "get", "MISS")   -> 'MISS'                (returns the default)
#     hasattr([], "append")       -> False                 (CPython: True)
#     setattr(p, "x", 99)         -> NotImplementedError
#   So dynamic attribute *resolution* as a meaningful feature does NOT work on
#   Monty; only the degenerate "always-miss" forms run.
#
# CPython 3.14.3: all of these resolve the real attribute/method.
#
# Strata front end: no handler for getattr/setattr/hasattr (no match in
# PythonToLaurel.lean); frontend-subset.md:328-332 lists dynamic attribute access
# (non-literal name) as OUT — the from_ClassInstance encoding has a fixed
# attribute schema.
#
# Matrix cell: (F) — BOTH exclude dynamic attribute access. Monty ships
# always-miss stubs; Frontend excludes the feature. Free simplification: Frontend
# never has to model the tp_getattro slot protocol, because Monty programs
# cannot meaningfully use dynamic attribute resolution anyway.
#
# This program is in Monty's subset (dict/list/str builtins only — no classes,
# whose instance attributes are runtime-NotImplemented on Monty 0.0.18).

d = {"a": 1, "b": 2}

# (1) hasattr is always False on Monty, even for a real method:
has_keys = hasattr(d, "keys")            # Monty: False   | CPython: True

# (2) getattr with a default returns the default, even when the attr exists:
got = getattr(d, "keys", "MISSED")       # Monty: 'MISSED'| CPython: <bound method>

# Observable (kept comparable across runtimes): both facts as a tuple.
[has_keys, got == "MISSED"]

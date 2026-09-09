# Feature: `with` / CONTEXT MANAGERS (out-of-worklist; follows item 6 exceptions).
#
# Headline: Monty and Frontend BOTH "support `with`", but their supported
# context-manager SETS ARE DISJOINT, so the usable intersection within Monty's
# subset is empty.
#
#   Monty's CMs : built-in types only (open() file objects). NO user classes
#                 (Monty has no runnable classes -> user __enter__/__exit__ is
#                 NotImplementedError). Confirmed on pydantic-monty 0.0.18:
#                   with x as y (x:int, non-CM)        -> TypeError   (MATCH CPython)  => `with` parses+executes
#                   with CM() as x (user-class CM)     -> NotImplementedError (CPython: 42)  => user CMs unusable
#                   with open(...)                     -> NotImplementedError on the bare harness (no FS mounted)
#   Frontend's CMs: user-defined classes with __enter__/__exit__ (the from_ClassInstance
#                 protocol). open()/file CMs are NOT in the subset ("may be added
#                 later", frontend-subset.md:363-366). __exit__/finally side effects
#                 are dropped (pending test_with_statement.py FakeCtx +
#                 test_soundness_finally_with_except.py).
#
# So a program in MONTY's subset can only use `with open(...)`, which Frontend
# cannot verify (open/filesystem OUT) -> Monty IN, Frontend OUT -> cell (C).
#
# This program is Monty's canonical `with` (a file context manager). It is in
# Monty's subset; on the bare differential harness (no mounted filesystem) the
# open() surfaces NotImplementedError, but the `with` machinery itself is
# confirmed to parse and execute by the non-CM TypeError probe above.

with open("data.txt") as f:
    contents = f.read()

# Observable (would be the file contents with a mounted FS). On Monty's built-in
# file CM, __exit__ closes the file on every exit path (with.md). Frontend has no
# model for open() / file effects, so it cannot translate this program at all.
len(contents)

#!/usr/bin/env python3
"""Normalize unstable assertion-label IDs in pyAnalyzeLaurel output.

When a verification obligation has no property summary, pyAnalyzeLaurel falls
back to printing the raw obligation label, which embeds internal IDs like
`main_assert(471)_32`. These IDs shift whenever the pipeline's internal
numbering changes, so the golden `.expected` files store a normalized form:
`name(NNN)` and `name(NNN)_NNN` both become `name(…)`.

Only labels whose parenthesized content is purely numeric and whose text after
the `)` is empty or a bare `_NNN` counter are normalized. Labels with
meaningful suffixes (e.g. `assert_assert(71)_calls_Any_get_0`) and
user-provided property summaries are left untouched.

This mirrors the normalization previously done in the Lean `#eval` golden
test (StrataPythonTestExtra/AnalyzeGoldenTest.lean); keep the two in sync.

Reads stdin, writes normalized output to stdout.
"""
import re
import sys

# Match: "<prefix> - <name>(<digits>)<after>"
# The label token is everything after the last " - " on the line.
_PATTERN = re.compile(r'^(.*? - )([^ ]*)\(([0-9]+)\)(.*)$')


def normalize_line(line: str) -> str:
    m = _PATTERN.match(line)
    if not m:
        return line
    prefix, name, _digits, after = m.group(1), m.group(2), m.group(3), m.group(4)
    # after ")" must be empty, or exactly a bare "_<digits>" uniqueness counter.
    if after == "" or re.fullmatch(r'_[0-9]+', after):
        return f"{prefix}{name}(…)"
    return line


def main() -> int:
    for line in sys.stdin:
        sys.stdout.write(normalize_line(line.rstrip('\n')) + '\n')
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Python `re` oracle for the regex differential test.

Reads tab-separated `<regex>\t<string>\t<mode>` triples from stdin (one per
line) and writes `<regex>\t<string>\t<mode>\t<result>` to stdout, where
<result> is one of:
  match
  noMatch
  error:<msg>

<mode> is one of match / fullmatch / search. The corpus is guaranteed tab- and newline-free
(see RegexDiffTest.lean), so a plain split on tab is safe.
"""

import re
import sys

_FNS = {"match": re.match, "fullmatch": re.fullmatch, "search": re.search}


def run(regex: str, string: str, mode: str) -> str:
    fn = _FNS.get(mode)
    if fn is None:
        return f"error:unknown mode {mode}"
    try:
        return "match" if fn(regex, string) is not None else "noMatch"
    except re.error as e:
        return f"error:{e}"


def main() -> int:
    out = []
    for line in sys.stdin:
        line = line.rstrip("\n")
        if not line:
            continue
        parts = line.split("\t")
        if len(parts) != 3:
            out.append(f"<bad>\t<bad>\t<bad>\terror:bad_input_format")
            continue
        regex, string, mode = parts
        out.append(f"{regex}\t{string}\t{mode}\t{run(regex, string, mode)}")
    sys.stdout.write("\n".join(out) + ("\n" if out else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())

r"""The regular-expression cases of `py.reSearch`, with CPython 3.12's answers.

It prints the Lean module `StrataPythonTest/Dyn/Sem/Contracts/RegexCases.lean`: each case is
`(pattern, string, verdict)`, with the verdict one of:

* `True` or `False`: what `re.search(pattern, string) is not None` gives on CPython 3.12;
* `gap`: the rule must stop with a gap, because the pattern is outside the subset that
  `Regex.lean` reads (this script knows which ones it built outside it), or CPython's compiler
  raises or warns on it, or it nests more than 20 groups.

No verdict comes from the Lean parser, so no case compares the parser with itself.  Before it
prints, it checks that `re`'s classes `\d`, `\w` and `\s` are `str.isdecimal`, `str.isalnum` or
`_`, and `str.isspace` on every code point, which the Lean side's classes are.

    python3.12 -I regex_cases.py > ../Sem/Contracts/RegexCases.lean
"""

import random
import re
import sys
import warnings


ALPHABET = ["a", "b", "_", "1", " ", "]", "[", "-", "\x08", "\n", "\t", "\r", "\x0b", "\x0c",
            "\x1c", "\x1d", "\x1e", "\x1f", "é", "٣"]
MAX_DEPTH = 20

# Patterns outside the subset: the rule stops with a gap on each, whatever CPython gives.
OUTSIDE = [
    r"(?=a)a", r"(?!a)b", r"(?<=a)b", r"(?<!a)b", r"(a)\1", r"(?P<x>a)(?P=x)",
    r"(?i)a", r"(?s).", r"(?m)^a", r"(?a)\w", r"(?>a+)a", r"a*+a", r"a++", r"a?+", r"a{2}+",
    # Counts above 1000, or written with more than 4 digits.
    r"a{1001}", r"a{00001}", r"a{2,1001}", r"a{1,00001}",
    r"(?(1)a|b)", r"\N{LATIN SMALL LETTER A}", r"\U00000061", r"\0", r"\141",
    r"\a", r"a{", r"a{x}", r"a{,}", r"a{1,2", r"\é", r"(?#c)a",
]

# Patterns of the subset's syntax that CPython rejects or warns on, and near misses that it reads.
HAND = [
    # A quantifier on an assertion, or with nothing before it, or after another quantifier.
    r"^*", r"$+", r"\b?", r"\A{2}", r"\Z*", r"\B+", r"(?:^)*", r"(\b)+",
    r"*a", r"a|*", r"(*)", r"a**", r"a{2}{3}", r"a{2}*", r"a*??", r"a*?*", r"{2}", r"{,2}",
    r"a|{2}",
    # Counts.
    r"a{3,2}", r"a{0}", r"a{0,0}", r"a{1000}", r"a{0001}", r"a{,3}",
    r"a{2,}", r"^a{2}$", r"^(?:a|b){2,3}$",
    # Sets: ranges, negation, a leading `]`, `\b` as a backspace, the warnings.
    r"[z-a]", r"[\w-a]", r"[a-\d]", r"[]a]", r"[]", r"[a", r"[\b]", r"[^a]", r"[^]a]",
    r"[a-]", r"[-a]", r"[a[]", r"[^[a]", r"[[a]", r"[[]", r"[a--b]", r"[a&&b]", r"[a~~b]",
    r"[a||b]", r"[]&&]", r"[^a&&]", r"[a-b--]", r"[--a]", r"[&&a]", r"[^&&]", r"[!--]", r"[---]",
    r"[\d_]", r"[^\s]", r"[\x41-\x5a]",
    # Escapes and groups.
    r"\x4", r"\x41", "a\\", r"(abc", r"abc)", r"(?P<1a>x)", r"(?P<>x)", r"(?P<a b>x)",
    r"(?P<a>x)(?P<a>y)", r"(?P<a>x)(?P<b>y)", r"()", r"(?:)", r"()*", r"\.", r"\-", r"\ ",
    r"\n", r"\t", r"\x0b", r"\v", r"\f", r"\r", r"[\r\f]", r"\]", r"[\]]", r"\[",
    # Assertions.
    r"\B", r"^\B$", r"a$", r"a\Z", r"^$", r"\A\Z", r"\bfoo\b", r"\Ba", r"$", r"^",
    # Classes on every character of the alphabet.
    r"\d", r"\D", r"\w", r"\W", r"\s", r"\S", r".", r"\b", r"[\s]", r"[\w]",
    # Nesting.
    "(" * 20 + "a" + ")" * 20, "(" * 21 + "a" + ")" * 21, "(b|" * 20 + "c" + ")*" * 20,
    # PySpec's patterns.
    r"^[a-z0-9-]+$", r"a+", r"b+", r"^[a-zA-Z]+$",
]


def depth(pattern):
    """The deepest group nesting of `pattern`, counting `(` and `)` outside sets and escapes."""
    d = best = 0
    i, in_set = 0, False
    while i < len(pattern):
        c = pattern[i]
        if c == "\\":
            i += 2
            continue
        if in_set:
            if c == "]":
                in_set = False
        elif c == "[":
            in_set = True
            if pattern[i + 1:i + 2] == "]":
                i += 1
        elif c == "(":
            d += 1
            best = max(best, d)
        elif c == ")":
            d -= 1
        i += 1
    return best


def verdict(pattern, string, outside):
    if outside or depth(pattern) > MAX_DEPTH:
        return "gap"
    with warnings.catch_warnings():
        warnings.simplefilter("error")
        try:
            compiled = re.compile(pattern)
        except (re.error, ValueError, OverflowError, RecursionError, Warning):
            return "gap"
    return "True" if compiled.search(string) is not None else "False"


class Gen:
    """Random patterns of the subset's grammar."""

    LITERALS = ["a", "b", "_", "1", " ", "-", r"\.", r"\n", r"\t"]
    CLASSES = [r"\d", r"\D", r"\w", r"\W", r"\s", r"\S", "."]
    ASSERTIONS = ["^", "$", r"\A", r"\Z", r"\b", r"\B"]

    def __init__(self, rng):
        self.rng = rng
        self.names = 0

    def set_(self):
        items = []
        for _ in range(self.rng.randint(1, 3)):
            k = self.rng.random()
            if k < 0.4:
                items.append(self.rng.choice(["a", "b", "_", "1", " ", r"\n"]))
            elif k < 0.7:
                lo, hi = sorted(self.rng.sample("ab1_", 2))
                items.append(f"{lo}-{hi}")
            else:
                items.append(self.rng.choice([r"\d", r"\w", r"\s", r"\D", r"\W", r"\S"]))
        return "[" + ("^" if self.rng.random() < 0.3 else "") + "".join(items) + "]"

    def atom(self, d):
        k = self.rng.random()
        if d > 0 and k < 0.15:
            return self.group(d - 1)
        if k < 0.45:
            return self.rng.choice(self.LITERALS)
        if k < 0.65:
            return self.rng.choice(self.CLASSES)
        if k < 0.8:
            return self.set_()
        return self.rng.choice(self.ASSERTIONS)

    def quant(self):
        q = self.rng.choice(["*", "+", "?", "{2}", "{1,}", "{,2}", "{0,2}", "{1,3}"])
        return q + ("?" if self.rng.random() < 0.3 else "")

    def seq(self, d):
        out = []
        for _ in range(self.rng.randint(0, 3)):
            a = self.atom(d)
            if a not in self.ASSERTIONS and self.rng.random() < 0.35:
                a += self.quant()
            out.append(a)
        return "".join(out)

    def alt(self, d):
        return "|".join(self.seq(d) for _ in range(self.rng.randint(1, 2)))

    def group(self, d):
        k = self.rng.random()
        if k < 0.4:
            return "(" + self.alt(d) + ")"
        if k < 0.8:
            return "(?:" + self.alt(d) + ")"
        self.names += 1
        return f"(?P<g{self.names}>" + self.alt(d) + ")"

    def pattern(self):
        self.names = 0
        return self.alt(2)


def strings(rng):
    out = [""] + list(ALPHABET)
    for _ in range(18):
        out.append("".join(rng.choice(ALPHABET) for _ in range(rng.randint(2, 6))))
    return out


def rows():
    rng = random.Random(20261106)
    gen = Gen(rng)
    patterns = [(p, True) for p in OUTSIDE] + [(p, False) for p in HAND]
    seen = {p for p, _ in patterns}
    while len(patterns) < len(OUTSIDE) + len(HAND) + 300:
        p = gen.pattern()
        if p not in seen:
            seen.add(p)
            patterns.append((p, False))
    for p, outside in patterns:
        for s in strings(rng):
            yield p, s, verdict(p, s, outside)


def check_classes():
    """`re`'s classes are the str predicates on every code point."""
    for cp in range(0x110000):
        c = chr(cp)
        if (re.match(r"\d", c) is not None) != c.isdecimal() \
                or (re.match(r"\w", c) is not None) != (c.isalnum() or c == "_") \
                or (re.match(r"\s", c) is not None) != c.isspace():
            sys.exit(f"re's classes differ from the str predicates at U+{cp:04X}")


def lean_str(t):
    out = []
    for c in t:
        if c == "\\":
            out.append("\\\\")
        elif c == '"':
            out.append('\\"')
        elif 0x20 <= ord(c) < 0x7F:
            out.append(c)
        else:
            assert ord(c) <= 0xFFFF, "Lean's \\u escape takes exactly four hex digits"
            out.append(f"\\u{ord(c):04X}")
    return '"' + "".join(out) + '"'


HEADER = """/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! Generated by `StrataPythonTest/Dyn/contract_rules/regex_cases.py` from CPython 3.12; do not
edit. Each case: the pattern, the string, and the verdict (`True`, `False` or `gap`). -/

namespace StrataPython.Dyn.Sem.Contracts.RegexCases

public section
"""

CHUNK = 1000


def main():
    if sys.version_info[:2] != (3, 12):
        sys.exit(f"regex_cases.py needs CPython 3.12, not {sys.version.split()[0]}")
    check_classes()
    cases = list(rows())
    chunks = [cases[i:i + CHUNK] for i in range(0, len(cases), CHUNK)]
    out = [HEADER]
    for k, chunk in enumerate(chunks):
        out.append(f"def cases{k} : Array (String × String × String) := #[")
        out.append(",\n".join(f"  ({lean_str(p)}, {lean_str(t)}, {lean_str(v)})" for p, t, v in chunk))
        out.append("]\n")
    out.append("/-- Every case. -/")
    out.append("def cases : Array (String × String × String) :=")
    out.append("  " + " ++ ".join(f"cases{k}" for k in range(len(chunks))))
    out.append("\nend\n\nend StrataPython.Dyn.Sem.Contracts.RegexCases")
    print("\n".join(out))


if __name__ == "__main__":
    main()

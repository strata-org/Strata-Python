#!/usr/bin/env python3
"""Generate the rule-validity case corpus.

    python3.13 tests/rule_validity_gen.py           # writes the case file

A case is an admitted module that exercises one rule, and nothing else. It
carries no expected outcome: `rule_validity.py` executes it under CPython and
takes that as the oracle, so a case can only be wrong by failing to reach the
rule -- never by encoding a wrong expectation. That is why this file is sources
and not a table of answers.

The bytes cases are generated because they are uniform. The syntax and transfer
cases are written out because each has to reach a specific protocol step, and a
template cannot know whether it did.
"""

from __future__ import annotations

import json
import os

import sys as _sys, os as _os
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
import paths
paths.on_path()
OUT = paths.data("rule_validity_cases.json")

# `bytes` literals are outside the admitted subset, so a bytes receiver arrives
# through `str.encode`, and every bytes-typed argument does too.
BYTES_SETUP = 'b = "Alpha Beta".encode()\n'

#: rule suffix -> the expressions to bind. A second entry is a distinct outcome
#: for the same rule, usually the raising one.
BYTES: dict[str, list[tuple[str, str]]] = {
    "capitalize": [("normal", "b.capitalize()")],
    "center": [("width", "b.center(20)"),
               ("fill", 'b.center(20, "-".encode())')],
    "count": [("normal", 'b.count("a".encode())')],
    "decode": [("normal", "b.decode()")],
    "endswith": [("normal", 'b.endswith("a".encode())')],
    "expandtabs": [("normal", "b.expandtabs()")],
    "find": [("present", 'b.find("A".encode())'),
             ("absent", 'b.find("zz".encode())')],
    "fromhex": [("normal", 'b.fromhex("41")')],
    "hex": [("normal", "b.hex()")],
    "index": [("present", 'b.index("A".encode())'),
              ("absent", 'b.index("zz".encode())')],
    "isalnum": [("normal", "b.isalnum()")],
    "isalpha": [("normal", "b.isalpha()")],
    "isascii": [("normal", "b.isascii()")],
    "isdigit": [("normal", "b.isdigit()")],
    "islower": [("normal", "b.islower()")],
    "isspace": [("normal", "b.isspace()")],
    "istitle": [("normal", "b.istitle()")],
    "isupper": [("normal", "b.isupper()")],
    "join": [("normal", '"-".encode().join([b, b])')],
    "ljust": [("normal", "b.ljust(20)")],
    "lower": [("normal", "b.lower()")],
    "lstrip": [("default", "b.lstrip()"),
               ("chars", 'b.lstrip("Al".encode())')],
    "maketrans": [("normal", 'b.maketrans("a".encode(), "b".encode())')],
    "partition": [("present", 'b.partition(" ".encode())'),
                  ("absent", 'b.partition("zz".encode())'),
                  ("empty_separator", 'b.partition("".encode())')],
    "removeprefix": [("normal", 'b.removeprefix("Al".encode())')],
    "removesuffix": [("normal", 'b.removesuffix("ta".encode())')],
    "replace": [("normal", 'b.replace("a".encode(), "b".encode())')],
    "rfind": [("present", 'b.rfind("a".encode())'),
              ("absent", 'b.rfind("zz".encode())')],
    "rindex": [("present", 'b.rindex("a".encode())'),
               ("absent", 'b.rindex("zz".encode())')],
    "rjust": [("normal", "b.rjust(20)")],
    "rpartition": [("normal", 'b.rpartition(" ".encode())'),
                   ("empty_separator", 'b.rpartition("".encode())')],
    "rsplit": [("default", "b.rsplit()"),
               ("sep", 'b.rsplit(" ".encode())'),
               ("empty_separator", 'b.rsplit("".encode())')],
    "rstrip": [("normal", "b.rstrip()")],
    "split": [("default", "b.split()"),
              ("sep", 'b.split(" ".encode())'),
              ("empty_separator", 'b.split("".encode())')],
    "splitlines": [("normal", "b.splitlines()")],
    "startswith": [("normal", 'b.startswith("A".encode())')],
    "strip": [("normal", "b.strip()")],
    "swapcase": [("normal", "b.swapcase()")],
    "title": [("normal", "b.title()")],
    "translate": [
        ("normal", 'b.translate(b.maketrans("a".encode(), "b".encode()))')],
    "upper": [("normal", "b.upper()")],
    "zfill": [("normal", "b.zfill(20)")],
}

# A class with an attribute, reused by the attribute cases.
OBJ = "class C:\n    def __init__(self):\n        self.x = 1\n\no = C()\n"

# `Required` and `NotRequired` are 3.11; `ReadOnly` is 3.13 (PEP 705), so it is
# imported only by the case that needs it, which carries `min_python`. Importing
# it here made four cases raise `ImportError` under the 3.12 the build host
# provides -- a portability bug in the corpus, not a finding about the analyzer.
TD = (
    "from typing import TypedDict, Required, NotRequired\n"
    "\n"
    "class T(TypedDict):\n"
)

TD_READONLY = (
    "from typing import TypedDict, ReadOnly\n"
    "\n"
    "class T(TypedDict):\n"
)

#: rule key -> cases. Each source is a whole admitted module.
SYNTAX: dict[str, list[tuple[str, str]]] = {
    "expr:name": [
        ("read", "a = 1\nb = a\n"),
        ("rebound", 'a = 1\na = "x"\nb = a\n'),
    ],
    "expr:const": [
        ("each", 'i = 1\nf = 1.5\ns = "x"\nn = None\nt = True\nfa = False\n'),
    ],
    "expr:binop": [
        ("arithmetic", "i = 1 + 2\nd = 7 // 2\nm = 7 % 2\np = 2 ** 3\n"),
        ("true_divide_is_float", "f = 4 / 2\n"),
        ("str_concat", 's = "a" + "b"\nr = "a" * 3\n'),
        ("mixed_int_float", "v = 1 + 1.5\n"),
        ("zero_division", "v = 1 // 0\n"),
        ("str_plus_int", 'v = "a" + 1\n'),
    ],
    "expr:unary": [
        ("each", "a = -1\nb = +1\nc = ~1\nd = -1.5\n"),
        ("not_a_number", 'v = -"a"\n'),
    ],
    "expr:not": [
        ("each", "a = not 0\nb = not [1]\nc = not None\n"),
    ],
    "expr:boolAnd": [
        ("truthy_left_yields_right", 'a = 1 and "x"\n'),
        ("falsy_left_yields_left", 'a = 0 and "x"\n'),
    ],
    "expr:boolOr": [
        ("falsy_left_yields_right", 'a = 0 or "x"\n'),
        ("truthy_left_yields_left", 'a = 1 or "x"\n'),
    ],
    "expr:cmp": [
        ("ordering", "a = 1 < 2\nb = 2 <= 2\nc = 3 > 4\n"),
        ("chained", "a = 1 < 2 < 3\nb = 1 < 0 < 3\n"),
        ("equality_across_types", 'a = "a" == 1\nb = None is None\n'),
        ("membership", "a = 1 in [1, 2]\nb = 5 not in [1, 2]\n"),
        ("unorderable", 'v = "a" < 1\n'),
    ],
    "expr:ifexp": [
        ("takes_then", 'a = 1 if 1 else "x"\n'),
        ("takes_else", 'a = 1 if 0 else "x"\n'),
    ],
    "expr:call": [
        ("builtin", "n = len([1, 2])\ns = str(1)\n"),
        ("user", "def f(a):\n    return a + 1\n\nv = f(1)\n"),
        ("wrong_arity", "def f(a):\n    return a\n\nv = f()\n"),
    ],
    "expr:attr": [
        ("present", OBJ + "v = o.x\n"),
        ("absent", OBJ + "v = o.nosuch\n"),
    ],
    "expr:subscr": [
        ("list_in_range", "xs = [1, 2]\nv = xs[0]\n"),
        ("list_out_of_range", "xs = [1, 2]\nv = xs[5]\n"),
        ("dict_present", 'd = {"k": 1}\nv = d["k"]\n'),
        ("dict_absent", 'd = {"k": 1}\nv = d["other"]\n'),
        ("str_index", 's = "ab"\nv = s[0]\n'),
        ("tuple_index", 't = (1, "a")\nv = t[1]\n'),
        ("wrong_index_type", 't = (1, 2)\nv = t["k"]\n'),
    ],
    "expr:listlit": [("mixed", 'xs = [1, "a"]\nempty = []\n')],
    "expr:dictlit": [("mixed", 'd = {"a": 1, "b": "s"}\nempty = {}\n')],
    "expr:setlit": [("normal", "s = {1, 2}\n")],
    "expr:tuplelit": [("mixed", 't = (1, "a")\nempty = ()\n')],
    "expr:fstr": [("interpolates", 'n = 1\ns = f"n={n}"\n')],
    "expr:listComp": [
        ("normal", "xs = [i + 1 for i in range(3)]\n"),
        ("filtered", "xs = [i for i in range(5) if i > 2]\n"),
    ],
    "expr:setComp": [("normal", "s = {i for i in range(3)}\n")],
    "expr:dictComp": [("normal", "d = {i: str(i) for i in range(3)}\n")],
    "expr:genComp": [
        ("lazy", "g = (i for i in range(3))\nvals = list(g)\n"),
    ],
    "expr:yield": [
        ("values", "def g():\n    yield 1\n    yield 2\n\nvals = list(g())\n"),
    ],
    "expr:yieldFrom": [
        ("delegates", "def g():\n    yield from [1, 2]\n\nvals = list(g())\n"),
    ],
    "target:name": [
        ("retypes", 'a = 1\na = "x"\n'),
    ],
    "target:tuple": [
        ("from_tuple", 'a, b = 1, "x"\n'),
        ("from_list", "a, b = [1, 2]\n"),
        ("length_mismatch", "a, b = [1, 2, 3]\n"),
    ],
    "target:attr": [
        ("retypes", OBJ + 'o.x = "s"\nv = o.x\n'),
        ("new_attribute", OBJ + "o.y = 2\nv = o.y\n"),
    ],
    "target:subscript": [
        ("list_slot", 'xs = [1, 2]\nxs[0] = "s"\nv = xs[0]\n'),
        ("dict_insert", 'd = {}\nd["k"] = 1\nv = d["k"]\n'),
        ("list_out_of_range", "xs = [1]\nxs[5] = 1\n"),
        ("immutable_receiver", 't = (1, 2)\nt[0] = 1\n'),
    ],
    "stmt:assign": [
        ("chained", "a = b = 1\n"),
        ("single", "a = 1\n"),
    ],
    "stmt:annAssign": [
        ("with_value", "a: int = 1\n"),
        ("bare_leaves_unbound", "a: int\nb = 1\n"),
    ],
    "stmt:exprS": [
        ("discards_value", "xs = [1]\nxs.append(2)\nn = len(xs)\n"),
    ],
    "stmt:pass": [("only", "pass\na = 1\n")],
    "stmt:if": [
        ("takes_else", 'a = 0\nif a:\n    v = 1\nelse:\n    v = "x"\n'),
        ("takes_then", 'a = 1\nif a:\n    v = 1\nelse:\n    v = "x"\n'),
        ("elif_chain",
         'n = 2\nif n == 1:\n    v = "one"\nelif n == 2:\n    v = 2\n'
         'else:\n    v = None\n'),
        ("no_else_may_leave_unbound", "a = 0\nif a:\n    v = 1\nn = 0\n"),
    ],
    "stmt:while": [
        ("counts", "i = 0\nwhile i < 3:\n    i = i + 1\n"),
        ("never_runs", 'i = 5\nv = "before"\nwhile i < 3:\n    v = 1\n'),
        ("else_runs_without_break",
         "i = 0\nwhile i < 2:\n    i = i + 1\nelse:\n    done = 1\n"),
    ],
    "stmt:for": [
        ("over_range", "t = 0\nfor i in range(3):\n    t = t + i\n"),
        ("over_list", 'last = None\nfor x in [1, "a"]:\n    last = x\n'),
        ("empty_leaves_target_unbound", "for x in []:\n    v = x\nn = 0\n"),
        ("else_runs_without_break",
         "for i in range(2):\n    pass\nelse:\n    done = 1\n"),
    ],
    "stmt:break": [
        ("exits_loop", "t = 0\nfor i in range(5):\n    if i == 2:\n"
                       "        break\n    t = t + i\n"),
        ("skips_else", "for i in range(5):\n    break\nelse:\n    done = 1\n"
                       "after = 1\n"),
    ],
    "stmt:continue": [
        ("skips_rest", "i = 0\nt = 0\nwhile i < 5:\n    i = i + 1\n"
                       "    if i == 2:\n        continue\n    t = t + i\n"),
    ],
    "stmt:return": [
        ("value", "def f():\n    return 1\n\nv = f()\n"),
        ("bare_returns_none", "def f():\n    return\n\nv = f()\n"),
        ("falls_off_end_returns_none", "def f():\n    a = 1\n\nv = f()\n"),
        ("from_branch", "def f(n):\n    if n:\n        return 1\n"
                        '    return "x"\n\nv = f(0)\n'),
    ],
    "stmt:raise": [
        ("caught", 'try:\n    raise ValueError("x")\nexcept ValueError as e:\n'
                   "    v = 1\n"),
        ("escapes", 'raise ValueError("x")\n'),
        ("from_function", 'def f():\n    raise KeyError("k")\n\nf()\n'),
    ],
    "stmt:try": [
        ("else_on_normal", "try:\n    v = 1\nexcept ValueError as e:\n"
                           "    v = 2\nelse:\n    w = 3\n"),
        ("handler_on_raise", "xs = [1]\ntry:\n    v = xs[5]\n"
                             "except IndexError as e:\n    v = 0\n"),
        ("finally_after_normal", "try:\n    v = 1\nfinally:\n    f = 1\n"),
        ("handler_matches_base", 'xs = [1]\ntry:\n    v = xs[5]\n'
                                 "except LookupError as e:\n    v = 0\n"),
        ("unmatched_escapes", 'xs = [1]\ntry:\n    v = xs[5]\n'
                              "except KeyError as e:\n    v = 0\n"),
    ],
    "stmt:assert": [
        ("holds", "a = 1\nassert a\nv = 2\n"),
        ("fails", "a = 0\nassert a\nv = 2\n"),
    ],
    "stmt:del": [
        ("name", "a = 1\nb = 2\ndel a\n"),
        # `del` on a subscript would move a container's shape mid-analysis, so
        # the subset rejects it rather than modelling it. Recorded here so the
        # boundary is asserted and not merely asserted-about.
        ("dict_key_rejected", 'd = {"k": 1}\ndel d["k"]\n', "rejected"),
    ],
    "ann:atom": [
        ("int_holds", "a: int = 1\n"),
        ("str_holds", 'a: str = "x"\n'),
    ],
    "ann:generic": [
        ("list_of_int", "xs: list[int] = [1, 2]\nv = xs[0]\n"),
        ("dict_of_str_int", 'd: dict[str, int] = {"a": 1}\nv = d["a"]\n'),
    ],
    "ann:union": [
        ("takes_int", "a: int | None = 1\n"),
        ("takes_none", "a: int | None = None\n"),
    ],
    "ann:literal": [
        ("holds", 'from typing import Literal\n\na: Literal["x"] = "x"\n'),
    ],
    "ann:any": [
        ("admits_anything", "from typing import Any\n\na: Any = 1\n"),
    ],
    "ann:required": [
        ("present", TD + "    a: Required[int]\n\nt: T = {\"a\": 1}\n"
                    'v = t["a"]\n'),
    ],
    "ann:notRequired": [
        ("absent_key_raises",
         TD + "    a: Required[int]\n    b: NotRequired[str]\n\n"
         't: T = {"a": 1}\nv = t["b"]\n'),
        ("present_key_reads",
         TD + "    a: Required[int]\n    b: NotRequired[str]\n\n"
         't: T = {"a": 1, "b": "s"}\nv = t["b"]\n'),
    ],
    "ann:readOnly": [
        ("reads", TD_READONLY + "    a: ReadOnly[int]\n\nt: T = {\"a\": 1}\n"
                 'v = t["a"]\n', None, (3, 13)),
    ],
}

#: transfer claim id -> cases. These reach a specific step of a hand-written
#: protocol walk, which is why each is written rather than generated.
TRANSFERS: dict[str, list[tuple[str, str]]] = {
    "transfer:truth-bool-then-len": [
        ("dunder_bool_wins",
         "class C:\n    def __bool__(self):\n        return False\n"
         "    def __len__(self):\n        return 5\n\n"
         'o = C()\nv = 1 if o else "x"\n'),
        ("falls_back_to_len",
         "class C:\n    def __len__(self):\n        return 0\n\n"
         'o = C()\nv = 1 if o else "x"\n'),
        ("neither_is_true",
         "class C:\n    def __init__(self):\n        self.x = 1\n\n"
         'o = C()\nv = 1 if o else "x"\n'),
        ("bool_returning_non_bool",
         "class C:\n    def __bool__(self):\n        return 1\n\n"
         'o = C()\nv = 1 if o else "x"\n'),
    ],
    "transfer:binop-reflected-on-notimplemented": [
        ("radd_runs",
         "class C:\n    def __radd__(self, other):\n        return 7\n\n"
         "o = C()\nv = 1 + o\n"),
        ("both_decline",
         "class C:\n    def __init__(self):\n        self.x = 1\n\n"
         "o = C()\nv = 1 + o\n"),
    ],
    "transfer:binop-subclass-reflected-first": [
        ("subclass_radd_precedes_base_add",
         "class B:\n    def __add__(self, other):\n        return 1\n"
         "    def __radd__(self, other):\n        return 2\n\n"
         "class D(B):\n    def __radd__(self, other):\n        return 3\n\n"
         "v = B() + D()\n"),
    ],
    "transfer:membership-contains-then-iter-then-getitem": [
        ("contains_wins",
         "class C:\n    def __contains__(self, item):\n        return True\n\n"
         "o = C()\nv = 99 in o\n"),
        ("iter_fallback",
         "class C:\n    def __iter__(self):\n        return iter([1, 2])\n\n"
         "o = C()\nv = 2 in o\n"),
        ("getitem_fallback",
         "class C:\n    def __getitem__(self, i):\n        if i > 1:\n"
         "            raise IndexError(i)\n        return i\n\n"
         "o = C()\nv = 1 in o\nw = 9 in o\n"),
    ],
    "transfer:membership-getitem-stop-is-false": [
        ("indexerror_subclass_means_absent",
         "class PastEnd(IndexError):\n    pass\n\n"
         "class C:\n    def __getitem__(self, i):\n        if i > 1:\n"
         "            raise PastEnd(i)\n        return i\n\n"
         "o = C()\nv = 9 in o\n"),
    ],
    "transfer:comparison-reflected": [
        ("reflected_lt",
         "class C:\n    def __gt__(self, other):\n        return True\n\n"
         "o = C()\nv = 1 < o\n"),
        ("eq_defaults_to_identity",
         "class C:\n    def __init__(self):\n        self.x = 1\n\n"
         "o = C()\np = C()\nsame = o == o\nother = o == p\n"),
    ],
    "transfer:iteration-getitem-fallback": [
        ("no_iter_uses_getitem",
         "class C:\n    def __getitem__(self, i):\n        if i > 2:\n"
         "            raise IndexError(i)\n        return i\n\n"
         "seen = []\nfor x in C():\n    seen.append(x)\n"),
    ],
    "transfer:iteration-stopiteration-ends-loop": [
        ("generator_exhausts",
         "def g():\n    yield 1\n    yield 2\n\n"
         "seen = []\nfor x in g():\n    seen.append(x)\n"),
        ("empty_body_never_runs",
         'v = "before"\nfor x in []:\n    v = x\n'),
    ],
    "transfer:iteration-unpack-arity": [
        ("pairs_unpack",
         'd = {"a": 1}\nks = []\nfor k, v in d.items():\n    ks.append(k)\n'),
        ("wrong_arity_raises", "for a, b in [(1, 2, 3)]:\n    v = a\n"),
    ],
    "transfer:attr-instance-then-mro": [
        ("instance_shadows_class",
         "class B:\n    def m(self):\n        return 1\n\n"
         "class D(B):\n    def m(self):\n        return 2\n\n"
         "v = D().m()\n"),
        ("inherited_from_base",
         "class B:\n    def m(self):\n        return 1\n\n"
         "class D(B):\n    def __init__(self):\n        self.x = 1\n\n"
         "v = D().m()\n"),
    ],
    "transfer:attr-miss-is-attributeerror": [
        ("miss_raises",
         "class C:\n    def __init__(self):\n        self.x = 1\n\n"
         "o = C()\nv = o.nosuch\n"),
        # The hook that would otherwise answer the miss is not admitted, which
        # is what makes the AttributeError above the whole answer.
        ("getattr_hook_rejected",
         "class C:\n    def __getattr__(self, name):\n        return 7\n\n"
         "o = C()\nv = o.nosuch\n", "rejected"),
    ],
    "transfer:attr-write-then-read": [
        ("write_visible",
         "class C:\n    def __init__(self):\n        self.x = 1\n\n"
         'o = C()\no.x = "s"\nv = o.x\n'),
    ],
    "transfer:subscript-getitem-dunder": [
        ("user_getitem",
         "class C:\n    def __getitem__(self, i):\n        return i * 2\n\n"
         "o = C()\nv = o[3]\n"),
        ("getitem_raises",
         "class C:\n    def __getitem__(self, i):\n"
         "        raise KeyError(i)\n\n"
         "o = C()\nv = o[3]\n"),
    ],
    "transfer:subscript-setitem-dunder": [
        ("user_setitem",
         "class C:\n    def __init__(self):\n        self.seen = 0\n"
         "    def __setitem__(self, i, value):\n        self.seen = i\n\n"
         "o = C()\no[2] = 1\nv = o.seen\n"),
    ],
    "transfer:len-calls-dunder-len": [
        ("user_len",
         "class C:\n    def __len__(self):\n        return 3\n\n"
         "v = len(C())\n"),
        ("negative_len_raises",
         "class C:\n    def __len__(self):\n        return -1\n\n"
         "v = len(C())\n"),
        ("non_int_len_raises",
         'class C:\n    def __len__(self):\n        return "x"\n\n'
         "v = len(C())\n"),
        ("no_len_raises",
         "class C:\n    def __init__(self):\n        self.x = 1\n\n"
         "v = len(C())\n"),
    ],
    "transfer:str-calls-dunder-str": [
        ("user_str",
         'class C:\n    def __str__(self):\n        return "c"\n\n'
         "v = str(C())\n"),
        ("default_str_is_repr_like",
         "class C:\n    def __init__(self):\n        self.x = 1\n\n"
         "v = str(C())\n"),
    ],
    "transfer:dict-get-default": [
        ("missing_yields_default",
         'd = {"a": 1}\nv = d.get("zz")\nw = d.get("zz", 0)\n'),
        ("present_yields_value", 'd = {"a": 1}\nv = d.get("a")\n'),
    ],
    "transfer:dict-pop-missing": [
        ("missing_raises", 'd = {"a": 1}\nv = d.pop("zz")\n'),
        ("missing_with_default", 'd = {"a": 1}\nv = d.pop("zz", 0)\n'),
    ],
    "transfer:dict-setdefault-inserts": [
        ("inserts_and_returns",
         'd = {}\nv = d.setdefault("k", 1)\nn = len(d)\n'),
    ],
    "transfer:dict-update-keywords": [
        ("keyword_keys", 'd = {"a": 1}\nd.update(b=2)\nv = d["b"]\n'),
        ("mapping_arg", 'd = {"a": 1}\nd.update({"b": 2})\nv = d["b"]\n'),
    ],
    "transfer:dict-view-types": [
        ("keys_values_items",
         'd = {"a": 1}\nk = d.keys()\nv = d.values()\ni = d.items()\n'),
    ],
    "transfer:try-else-only-on-normal": [
        ("else_skipped_on_raise",
         'xs = [1]\nw = "before"\ntry:\n    v = xs[5]\n'
         "except IndexError as e:\n    v = 0\nelse:\n    w = 1\n"),
    ],
    "transfer:finally-on-every-completion": [
        ("after_raise",
         "xs = [1]\nf = 0\ntry:\n    v = xs[5]\nexcept IndexError as e:\n"
         "    v = 0\nfinally:\n    f = 1\n"),
        ("after_return",
         "def h():\n    try:\n        return 1\n    finally:\n"
         "        pass\n\nv = h()\n"),
        ("after_break",
         "f = 0\nfor i in range(3):\n    try:\n        break\n"
         "    finally:\n        f = 1\n"),
    ],
    "transfer:handler-matches-subclass": [
        ("base_catches_derived",
         "class MyError(ValueError):\n    pass\n\n"
         "try:\n    raise MyError(1)\nexcept ValueError as e:\n    v = 1\n"),
    ],
    "transfer:handler-target-cleanup": [
        ("target_unbound_after_handler",
         "xs = [1]\nkept = None\ntry:\n    v = xs[5]\n"
         "except IndexError as e:\n    kept = e\n    v = 0\nafter = 1\n"),
    ],
    "transfer:call-binds-positional-then-keyword": [
        ("by_keyword",
         'def f(a, b):\n    return a\n\nv = f(b=1, a="x")\n'),
        ("defaults_fill",
         "def f(a, b=2):\n    return b\n\nv = f(1)\n"),
        ("duplicate_argument",
         "def f(a):\n    return a\n\nv = f(1, a=2)\n"),
        ("unexpected_keyword",
         "def f(a):\n    return a\n\nv = f(a=1, c=2)\n"),
    ],
    "transfer:call-constructs-instance": [
        ("init_runs",
         "class C:\n    def __init__(self, n):\n        self.n = n\n\n"
         'o = C("x")\nv = o.n\n'),
        ("init_arity_checked",
         "class C:\n    def __init__(self, n):\n        self.n = n\n\n"
         "o = C()\n"),
    ],
    "transfer:loop-fixpoint-widens": [
        ("type_changes_across_iterations",
         'v = 0\nfor i in range(3):\n    v = "x" if i else 1\n'),
        ("accumulates",
         "xs = []\nfor i in range(3):\n    xs.append(i)\nn = len(xs)\n"),
    ],
    "transfer:comprehension-scope": [
        ("target_does_not_leak",
         "i = \"outer\"\nxs = [j for j in range(3)]\nv = i\n"),
        ("failing_element_abandons_binding",
         'xs = [1]\nbefore = "kept"\nbefore = [x for x in xs][5]\n'),
    ],
    "transfer:boolop-shortcircuits": [
        ("right_not_evaluated",
         "xs = []\nv = xs and xs[0]\n"),
        ("or_right_not_evaluated",
         "xs = [1]\nv = xs or xs[5]\n"),
    ],
    "transfer:fstring-formats": [
        ("calls_format",
         'class C:\n    def __str__(self):\n        return "c"\n\n'
         'o = C()\ns = f"{o}"\n'),
    ],
    "transfer:generator-raises-at-consumption": [
        ("body_raise_surfaces_in_loop",
         "def g():\n    yield 1\n    raise ValueError(2)\n\n"
         "seen = []\nfor x in g():\n    seen.append(x)\n"),
    ],
}


def build() -> list[dict]:
    cases: list[dict] = []
    for suffix, entries in sorted(BYTES.items()):
        for name, expression in entries:
            cases.append({
                "rule": f"bytes.{suffix}",
                "name": name,
                "source": BYTES_SETUP + f"r = {expression}\n",
            })
    for table in (SYNTAX, TRANSFERS):
        for rule, entries in sorted(table.items()):
            for entry in entries:
                name, source = entry[0], entry[1]
                case = {"rule": rule, "name": name, "source": source}
                if len(entry) > 2 and entry[2] is not None:
                    case["expect"] = entry[2]
                if len(entry) > 3 and entry[3] is not None:
                    case["min_python"] = list(entry[3])
                cases.append(case)
    return cases


def main() -> None:
    cases = build()
    with open(OUT, "w", encoding="utf-8") as handle:
        json.dump({"cases": cases}, handle, indent=1, sort_keys=True)
        handle.write("\n")
    rules = {case["rule"] for case in cases}
    print(f"{len(cases)} cases over {len(rules)} rules -> {OUT}")


if __name__ == "__main__":
    main()

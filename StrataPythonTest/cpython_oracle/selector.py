"""Decide which CPython test methods this suite can say anything about.

The filter tests ONE thing: does the generated program mean the same as the original
method? Anything Strata merely cannot handle yet is attempted deliberately -- the suite
exists to discover that, and a rejected construct is a finding. What is excluded is only
what would make the comparison invalid.

Selection is per METHOD, never per file. A file's import block says nothing about a
method that never references those names -- an unused import is free (the front end
accepts it and reports `Analysis success`), and a used-but-unmodelled one degrades its
obligations to `unknown`, which is sound.

Because `prepare.py` keeps the method in its class, most of what an earlier version had
to check has no reason to be checked. `self` is just `self`; a helper inherited from a
base class in the same file resolves by ordinary attribute lookup; class-body attributes
stay class attributes; `super()` and `__qualname__` work. The conditions that remain are
properties of the TEST, not of the emission.

Conditions, all required:
  * the class names TestCase among its bases
  * every assertion used is exactly lowerable by lower.py, in the method and in
    everything emitted alongside it. A method with NO assertion is fine -- it asserts
    that nothing raises, which the comparison already checks
  * nothing reached through `self` is missing from the emitted class. A base class from
    outside the file is DROPPED (see `prepare.classify_bases`), so a method using one of
    its helpers has nothing to dispatch to
  * `self` is not passed to an external callable. `check_syntax_error(self, 'x + 1 = 1')`
    hands the TestCase to a `test.support` helper that calls `self.assertRaisesRegex` on
    it, and the unittest base is dropped from the emitted class
  * no `exec`/`eval`/`compile`/`globals`/`locals`/`vars`. Such a method does run, and
    92 of them are recorded as agreeing -- but the assertion under test is inside a
    string the interpreter never evaluated, so the pass is vacuous and reads as coverage
    it has not earned
  * nothing that inspects a traceback or code positions: the generated file is a
    different file, so its line numbers differ by construction
  * `global`/`nonlocal` are allowed: inside the emitted method they still name module
    scope, the free-name check catches a global nothing defines, and the
    generated-program check catches anything subtler
  * every free name has a module-level definition the prelude can emit
"""
from __future__ import annotations

import ast

import lower
from prepare import classify_bases, method_table, needed_methods
from prepare import DYNAMIC_BUILTINS, module_defs as prepare_module_defs

# Assertions that lower exactly to a Python `assert`. Owned by lower.py.
MODELLED = lower.LOWERABLE

# Statement/expression shapes the generator will not carry over.
class _Reject(ast.NodeVisitor):
    def __init__(self) -> None:
        self.reasons: list[str] = []





    def visit_Attribute(self, n):
        # A test that inspects a traceback is asserting about its own source
        # positions, which the generated file necessarily changes. The
        # `test_exception_locations` family in test_iter, test_listcomps, test_setcomps
        # and test_dictcomps is exactly this, and it was caught by the
        # generated-program check rather than by inspection.
        if n.attr in ("__traceback__", "tb_lineno", "tb_frame", "co_firstlineno",
                      "co_positions"):
            self.reasons.append("source-position")
        self.generic_visit(n)

    def visit_Call(self, n):
        # `exec`/`eval`/`compile` run a code STRING, so the behaviour under test is not
        # in the AST and no translation can reach it. These methods DO run: the body is
        # copied verbatim, so the generated program behaves as the original does and 92
        # of them are recorded as agreeing. That agreement is the problem, not the
        # argument for keeping them -- `agree` means the interpreter ran to completion as
        # CPython did, and when the assertion under test lives inside the string the
        # interpreter never evaluated it. A vacuous pass is worse than a gap, because it
        # reads as coverage.
        #
        # Not the same judgement as attempting repr/type/id: a verdict on those is
        # meaningful even when it is negative.
        f = n.func
        if isinstance(f, ast.Name) and f.id in DYNAMIC_BUILTINS:
            self.reasons.append(f"dynamic:{f.id}")
        self.generic_visit(n)







def _module_level_stmts(tree: ast.Module):
    """Statements executed at module level.

    Descends into module-level control flow (`if`, `try`, `for`, `while`, `with`),
    because a binding inside `if sys.platform == ...:` is still module-level, but
    NOT into function or class bodies -- their locals are not module names, and
    treating them as such rejects nearly every method.
    """
    stack = list(tree.body)
    while stack:
        s = stack.pop()
        yield s
        if isinstance(s, (ast.If, ast.Try, ast.For, ast.AsyncFor, ast.While,
                          ast.With, ast.AsyncWith)):
            stack.extend(s.body)
            stack.extend(getattr(s, "orelse", []) or [])
            stack.extend(getattr(s, "finalbody", []) or [])
            for h in getattr(s, "handlers", []) or []:
                stack.extend(h.body)


def _is_testcase_base(b: ast.expr) -> bool:
    """Does this base express unittest's TestCase?

    Matched on the base's name rather than a substring of its source, so an
    unrelated identifier that merely contains "TestCase" is not accepted.
    """
    if isinstance(b, ast.Attribute):
        return b.attr == "TestCase"
    if isinstance(b, ast.Name):
        return b.id == "TestCase"
    return False


def _has_star_import(tree: ast.Module) -> bool:
    """`from x import *` binds names we cannot enumerate, so nothing is selectable."""
    return any(isinstance(s, ast.ImportFrom) and any(a.name == "*" for a in s.names)
               for s in _module_level_stmts(tree))


def _self_attrs(node) -> set[str]:
    """Attribute names reached through `self` anywhere under `node`."""
    return {n.attr for n in ast.walk(node)
            if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name)
            and n.value.id == "self"}




def _assigned_self_attrs(node) -> set[str]:
    """`self.X` names ASSIGNED under `node`."""
    out = set()
    for n in ast.walk(node):
        targets = []
        if isinstance(n, ast.Assign):
            targets = n.targets
        elif isinstance(n, (ast.AugAssign, ast.AnnAssign)):
            targets = [n.target]
        elif isinstance(n, (ast.For, ast.AsyncFor)):
            targets = [n.target]
        elif isinstance(n, (ast.With, ast.AsyncWith)):
            targets = [i.optional_vars for i in n.items if i.optional_vars]
        for t in targets:
            for x in ast.walk(t):
                if (isinstance(x, ast.Attribute) and isinstance(x.value, ast.Name)
                        and x.value.id == "self"):
                    out.add(x.attr)
    return out








# Decorators that only decide WHETHER CPython runs the test, and so are not part of
# what it means. They are dropped from the generated program; if CPython skips the
# test, there is no expectation and compare.py excludes it.
#
# `expectedFailure` is deliberately absent: it inverts the result rather than gating
# it, so dropping it would change the test. Anything that passes arguments
# (`bigmemtest`) is absent for the same reason.
_SKIP_ONLY_DECORATORS = frozenset({
    "skip", "skipIf", "skipUnless", "unittest.skip", "unittest.skipIf",
    "unittest.skipUnless", "cpython_only", "support.cpython_only",
    "test.support.cpython_only", "impl_detail", "support.impl_detail",
    "refcount_test", "support.refcount_test", "requires_resource",
    "support.requires_resource", "requires_IEEE_754", "support.requires_IEEE_754",
    "no_tracing", "support.no_tracing", "requires_docstrings",
    "support.requires_docstrings", "requires_limited_api",
    "requires_specialization", "skip_on_s390x", "check_bytes_warnings",
    "requires_subprocess", "support.requires_subprocess",
})


def _decorators_are_skip_only(fn: ast.FunctionDef) -> bool:
    for d in fn.decorator_list:
        head = ast.unparse(d).split("(")[0].strip()
        if head not in _SKIP_ONLY_DECORATORS:
            return False
    return True








def _assertion_calls(fn: ast.FunctionDef) -> list[ast.Call]:
    """Every `self.assertX(...)` or exactly-lowerable `self.X(...)` in `fn`.

    Covers both a statement and a `with` header, since assertRaises and subTest appear
    as either.
    """
    def is_self_call(e):
        return (isinstance(e, ast.Call) and isinstance(e.func, ast.Attribute)
                and isinstance(e.func.value, ast.Name) and e.func.value.id == "self"
                and (e.func.attr.startswith("assert")
                     or e.func.attr in lower.LOWERABLE_SELF))

    out = []
    for n in ast.walk(fn):
        c = lower.is_assertion_stmt(n)
        if c is not None:
            out.append(c)
        elif isinstance(n, ast.Expr) and is_self_call(n.value):
            out.append(n.value)
        if isinstance(n, ast.With):
            for item in n.items:
                if is_self_call(item.context_expr):
                    out.append(item.context_expr)
    return out


def _lowerable(fn: ast.FunctionDef, extra: list[ast.FunctionDef] = (),
               cls_body: list = ()) -> bool:
    """Does every assertion lower exactly, in `fn` AND in everything inlined with it?

    `extra` is setUp plus the helper methods. prepare.py lowers their bodies too, so
    checking only the test method leaves them free to carry an assertion we cannot
    lower -- which surfaced as test_descr.test_reduce failing generation with
    "unlowerable assertion", after the selector had already accepted it.

    This has to agree with prepare.py exactly. Where it did not, the selector accepted
    `with self.assertRaises(E) as cm:` -- which `lower.build_raises_with` refuses,
    because binding the exception means the assertions made about `cm.exception` would
    be silently dropped -- and generation then failed with "no lowered assertion".
    """
    calls = list(_assertion_calls(fn))
    for e in extra:
        calls += _assertion_calls(e)
    # A method with no assertion at all is NOT rejected: it asserts that nothing
    # raises, and comparing the interpreter's completion against CPython's checks
    # exactly that. 245 methods were being dropped for having nothing to lower.
    own_helpers = {x.name for x in cls_body if isinstance(x, ast.FunctionDef)}
    for c in calls:
        if c.func.attr in lower.LOWERABLE_SELF:
            continue
        # a custom assertion helper on the class is inlined, not lowered
        if c.func.attr in own_helpers:
            continue
        if c.func.attr in lower.RAISES:
            if lower.raises_exception(c) is None:
                return False
            continue
        if c.func.attr not in lower.LOWERABLE or lower.build(c) is None:
            return False
    # A multi-item `with` carrying an assertion, and a binding this lowering cannot
    # reproduce. `with self.assertRaises(E) as cm` IS supported: the exception is kept in
    # a local and `cm.exception` is rewritten to name it. What is refused is a binding
    # used any other way -- unittest also exposes `cm.msg`, and the assertWarns manager
    # has `warning`/`filename`/`lineno`, none of which the scaffold reproduces.
    for src in [fn, *extra]:
        for n in ast.walk(src):
            if not isinstance(n, ast.With):
                continue
            for item in n.items:
                e = item.context_expr
                if not (isinstance(e, ast.Call) and isinstance(e.func, ast.Attribute)
                        and isinstance(e.func.value, ast.Name)
                        and e.func.value.id == "self"
                        and (e.func.attr.startswith("assert")
                             or e.func.attr in lower.LOWERABLE_SELF)):
                    continue
                if len(n.items) != 1:
                    return False
                if item.optional_vars is None:
                    continue
                if e.func.attr in lower.LOWERABLE_SELF:
                    continue                      # subTest may bind freely
                cm = lower.with_binding(item)
                if cm is None:
                    return False                  # `as (a, b)` and the like
                if _binding_used_beyond_exception(src, cm):
                    return False
    return True


def _binding_used_beyond_exception(node: ast.AST, cm: str) -> bool:
    """Is `cm` touched anywhere except as `cm.exception`?"""
    for n in ast.walk(node):
        if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) \
                and n.value.id == cm:
            if n.attr != lower.CM_ATTR:
                return True
        elif isinstance(n, ast.Name) and n.id == cm and isinstance(n.ctx, ast.Load):
            # a bare `cm`, not an attribute access on it
            return True
    return False




def _unresolvable(tree: ast.Module, cls: ast.ClassDef, seeds: list[ast.AST],
                  helpers: list[str]) -> bool:
    """Is any free name in the generated program impossible to supply?

    prepare.py emits a prelude of module-level definitions, so a module-level name is
    fine. What is not fine is a name with nothing to bind it: it would make the
    generated program reference something that does not exist, and Strata's complaint
    would be about our emission rather than about Python.
    """
    import builtins
    defined = set(prepare_module_defs(tree))
    local = {cls.name} | set(helpers) | set(dir(builtins)) | {"self"}
    for s in seeds:
        bound = {n.id for n in ast.walk(s)
                 if isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store,
                                                                   ast.Del))}
        bound |= {x.name for x in ast.walk(s)
                  if isinstance(x, (ast.FunctionDef, ast.AsyncFunctionDef,
                                    ast.ClassDef))}
        bound |= {a.arg for x in ast.walk(s)
                  if isinstance(x, (ast.FunctionDef, ast.AsyncFunctionDef,
                                    ast.Lambda))
                  for a in x.args.args + x.args.kwonlyargs + x.args.posonlyargs}
        # `except E as e` and `except* E as e` are DISTINCT node types, and a match
        # capture binds through a plain string too -- none of them is a Store Name. A
        # later reference to the captured name would otherwise look free and the method
        # would be dropped, the same silent over-rejection as the local imports below.
        bound |= {h.name for x in ast.walk(s)
                  if isinstance(x, (ast.Try, ast.TryStar))
                  for h in x.handlers if h.name}
        bound |= {n for x in ast.walk(s)
                  if isinstance(x, (ast.MatchAs, ast.MatchStar))
                  for n in [x.name] if n}
        bound |= {x.rest for x in ast.walk(s)
                  if isinstance(x, ast.MatchMapping) and x.rest}
        # An import INSIDE the method body binds through `ast.alias`, not a Store Name.
        # `import gc` followed by a reference to `gc` is common in the CPython suite, and
        # without this the name looked free and the method was dropped -- an
        # over-rejection, where the point is to attempt everything that can mean the
        # same thing.
        bound |= {a.asname or a.name.split(".")[0] for x in ast.walk(s)
                  if isinstance(x, ast.Import) for a in x.names}
        bound |= {a.asname or a.name for x in ast.walk(s)
                  if isinstance(x, ast.ImportFrom) for a in x.names}
        bound |= {n.id for x in ast.walk(s)
                  if isinstance(x, (ast.comprehension,))
                  for n in ast.walk(x.target) if isinstance(n, ast.Name)}
        for n in ast.walk(s):
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load):
                if n.id not in defined and n.id not in local and n.id not in bound:
                    return True
    return False


def reject_reasons(fn: ast.FunctionDef) -> list[str]:
    """Why this method cannot be emitted meaning-preservingly, if anything."""
    r = _Reject()
    for st in fn.body:
        r.visit(st)
    return r.reasons


def _class_attr_names(cls: ast.ClassDef) -> set[str]:
    """Names bound in the class body, which its methods may reach bare or via `self`."""
    out: set[str] = set()
    for st in cls.body:
        if isinstance(st, ast.Assign):
            out |= {n.id for t in st.targets for n in ast.walk(t)
                    if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)}
        elif isinstance(st, ast.AnnAssign) and isinstance(st.target, ast.Name):
            out.add(st.target.id)
        elif isinstance(st, (ast.ClassDef, ast.FunctionDef)):
            out.add(st.name)
    return out


def _unreachable_self_attrs(fn: ast.FunctionDef, inlined: list[ast.FunctionDef],
                            cls: ast.ClassDef, table: dict[str, ast.FunctionDef],
                            base_defs: list[ast.ClassDef]) -> bool:
    """Does anything reached through `self` have nothing on the class to satisfy it?

    A kept base is emitted whole, so its class-body ATTRIBUTES are in the generated
    program too. `method_table` folds in inherited methods; the bases are needed here so
    a method reading an inherited attribute is not dropped as unreachable when the
    attribute is right there.
    """
    usable = set(table) | _class_attr_names(cls) | set(lower.LOWERABLE) \
        | set(lower.LOWERABLE_SELF)
    for b in base_defs:
        usable |= _class_attr_names(b)
    for node in [fn, *inlined]:
        usable |= _assigned_self_attrs(node)
    for node in [fn, *inlined]:
        for attr in _self_attrs(node):
            if attr.startswith("__") or attr in usable:
                continue
            return True
    return False


def _unreachable_super_calls(nodes: list[ast.AST],
                             base_defs: list[ast.ClassDef]) -> bool:
    """Does a `super().X()` reach past every base this program emits?

    `unittest.TestCase` is dropped, so `super().setUp()` in a class whose only base was
    the framework has nothing to resolve to and raises
    `AttributeError: 'super' object has no attribute 'setUp'`. A `super()` call that
    lands on a base defined in the same file is fine, since that base is emitted.
    """
    available: set[str] = set()
    for b in base_defs:
        available |= {x.name for x in b.body if isinstance(x, ast.FunctionDef)}
    for node in nodes:
        for n in ast.walk(node):
            if not (isinstance(n, ast.Attribute) and isinstance(n.value, ast.Call)):
                continue
            callee = n.value.func
            if (isinstance(callee, ast.Name) and callee.id == "super"
                    and n.attr not in available):
                return True
    return False


def _passes_self_to_external(nodes: list[ast.AST]) -> bool:
    """Is `self` handed to a callable that is not a method on this class?

    `test.support.check_syntax_error(self, 'x + 1 = 1')` is the pattern: an imported
    helper that takes the TestCase and calls `self.assertRaisesRegex` on it. The
    unittest base is dropped from the emitted class, so that API is not there and the
    program raises AttributeError -- 33 methods did. The helper is library code, so
    the alternative is a stub base reimplementing the unittest assertion API, which is
    modelling the very thing this suite lowers precisely to avoid.

    A bare `self` used any other way is fine: `self` exists, so `return self` or
    `self is other` needs nothing.
    """
    for node in nodes:
        for n in ast.walk(node):
            if not isinstance(n, ast.Call):
                continue
            external = not (isinstance(n.func, ast.Attribute)
                            and isinstance(n.func.value, ast.Name)
                            and n.func.value.id in ("self", "cls"))
            if not external:
                continue
            for a in list(n.args) + [k.value for k in n.keywords]:
                if isinstance(a, ast.Name) and a.id in ("self", "cls"):
                    return True
    return False


def select_file(source: str, relpath: str) -> list[dict]:
    """Selected methods in one CPython test file, for class-preserving emission."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []
    star = _has_star_import(tree)
    picked = []
    for cls in [c for c in ast.walk(tree) if isinstance(c, ast.ClassDef)]:
        if not any(_is_testcase_base(b) for b in cls.bases):
            continue
        _, base_defs = classify_bases(cls, tree)
        table = method_table(cls, base_defs)
        setup = table.get("setUp")
        setup_cls = table.get("setUpClass")
        fixtures = [f for f in (setup, setup_cls) if f is not None]
        if any(f.decorator_list and not _decorators_are_skip_only(f)
               or reject_reasons(f) for f in fixtures):
            continue
        for fn in [x for x in cls.body
                   if isinstance(x, ast.FunctionDef) and x.name.startswith("test")]:
            if not _decorators_are_skip_only(fn):
                continue
            if reject_reasons(fn):
                continue
            helpers = needed_methods(fn, table, fixtures) - {fn.name, "setUp",
                                                             "setUpClass"}
            inlined = [table[h] for h in sorted(helpers)] + fixtures
            if any(reject_reasons(h) for h in inlined):
                continue
            # Every assertion must lower exactly, in the method and in everything
            # emitted alongside it. This has to agree with prepare.py exactly, or
            # generation fails on a method selection already accepted.
            if not _lowerable(fn, inlined, cls.body):
                continue
            # Everything reached through `self` must exist on the emitted class. A base
            # from outside the file is DROPPED (see `classify_bases`), so a method using
            # one of its helpers would raise AttributeError -- 129 methods did, all
            # landing in `loweringBroken` where no verdict is drawn. Rejecting them here
            # states the real reason instead.
            if _unreachable_self_attrs(fn, inlined, cls, table, base_defs):
                continue
            if _passes_self_to_external([fn, *inlined]):
                continue
            if _unreachable_super_calls([fn, *inlined], base_defs):
                continue
            # The seeds must be what is actually EMITTED -- the kept methods, the
            # class-body attributes and the local base classes. Seeding only the methods
            # missed free names in the other two, and 108 programs died with
            # `NameError: name 'X' is not defined`.
            attr_stmts = [st for st in cls.body
                          if isinstance(st, (ast.Assign, ast.AnnAssign, ast.ClassDef))]
            seeds = [fn, *inlined, *attr_stmts, *base_defs]
            visible = sorted(set(table) | _class_attr_names(cls))
            if not star and _unresolvable(tree, cls, seeds, visible):
                continue
            picked.append({"file": relpath, "cls": cls.name, "method": fn.name,
                           "helpers": sorted(helpers)})
    return picked

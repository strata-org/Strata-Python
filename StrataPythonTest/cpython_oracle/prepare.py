"""Turn one selected CPython test method into a self-contained program Strata can run.

The method STAYS IN ITS CLASS. The program is the class, pruned to what the test needs,
plus a driver that instantiates it and calls the method:

    <prelude>                     module-level definitions the class needs
    class Base: ...               base classes defined in the same file
    class DictTests(Base):
        thetype = frozenset       class-body attributes, unchanged
        def setUp(self): ...      the fixture, unchanged
        def helper(self): ...     only the helpers this test calls
        def test_foo(self):
            pass                  see below
            assert self.d['a'] == 1    assertions lowered, `self` untouched
    _cpython_oracle_case = DictTests()
    _cpython_oracle_case.setUp()
    _cpython_oracle_case.test_foo()

An earlier version hoisted the body into a module-level function and rewrote `self.x` to
a local `self_x`. That was forced, not chosen: `pyInterpret` could not execute a program
that INSTANTIATED a class, because V2 left the synthetic `__main__` unmarked as an
interpret entry and GlobalParameterization therefore gave it an `inout $heap` parameter
nothing supplied. Once that was fixed, keeping the class measured **418 agreeing methods
against 88**, with `needsTriage` falling from 351 to 7 -- the hoisting version spent its
results on the rewrite rather than on Python.

Keeping the class also deletes the rewrite's four scope rules, every one of which had to
be discovered by a generated program misbehaving: a nested function shadows only the
parameter it declares; `self` can be bound by assignment rather than as a parameter; a
default argument is evaluated in the enclosing scope; a nested function writing fixture
state needs a `nonlocal`. None of them has anything to say about Python, and all four are
now moot. `super()` and `__qualname__` work for the same reason.

**THE CLASS IS PRUNED** to the test method, the fixtures, and the transitive closure of
helpers it calls. Emitting it whole would let one untranslatable sibling poison every
other method in the class, since the front end translates the whole class: `test_a` would
fail because `test_z` uses `exec`.

**`unittest.TestCase` is dropped.** Every assertion is lowered, so nothing inherited from
it is needed. A stub base reimplementing `assertEqual` and friends would be modelling the
very thing lowering exists to avoid. A base defined in the SAME FILE is kept, so an
inherited helper resolves by ordinary attribute lookup; a base from anywhere else is
dropped, since emitting it would mean translating `test.support`.

**A leading `pass`** goes in each emitted method. V2 promotes a leading run of `assert`
statements into that method's preconditions (`splitPreconditions`, Translation.lean), and
a generated body is often *entirely* asserts, so without a non-assert statement first
every assertion is hoisted into `requires` instead of staying a statement to execute.

**The prelude** carries the transitive closure of the module-level names the class
touches -- imports, helper classes, constants -- and the module-level MUTATIONS of them.
An import Strata cannot model is fine: attempting it is the point.

Emission is by `ast.unparse`, not line surgery. An earlier version kept the generated
file line-aligned with the CPython source because the verifier's per-obligation results
had to be joined back by location; the comparison is now per METHOD, so nothing joins on
location.

Whether any of this preserved meaning is not taken on trust: runner.py runs every
generated program under CPython and the run fails if one behaves differently from the
original method. That check found every rejection rule in this file.
"""
from __future__ import annotations

import ast
import copy

import lower











def _rewrite_cm(stmts: list[ast.stmt], cm: str, local: str) -> list[ast.stmt]:
    """`cm.exception` -> `local`, in the statements after a `with ... as cm` block.

    Any other attribute of `cm` is refused rather than approximated: unittest also
    exposes `cm.msg`, and the assertWarns manager has `warning`/`filename`/`lineno`,
    none of which this scaffold reproduces.
    """
    out = [copy.deepcopy(s) for s in stmts]
    for st in out:
        for n in ast.walk(st):
            for field, value in ast.iter_fields(n):
                if isinstance(value, list):
                    for i, item in enumerate(value):
                        if _is_cm_exception(item, cm):
                            value[i] = ast.Name(id=local, ctx=ast.Load())
                elif _is_cm_exception(value, cm):
                    setattr(n, field, ast.Name(id=local, ctx=ast.Load()))
    for st in out:
        for n in ast.walk(st):
            if (isinstance(n, ast.Name) and n.id == cm) or (
                    isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name)
                    and n.value.id == cm):
                raise ValueError(f"`{cm}` is used other than as `{cm}.exception`")
    return out


def _is_cm_exception(node, cm: str) -> bool:
    return (isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name)
            and node.value.id == cm and node.attr == lower.CM_ATTR)


class _Lower(ast.NodeTransformer):
    """Replace `self.assertX(...)` statements with the assert they mean."""

    def __init__(self, own_helpers: set[str] = frozenset()) -> None:
        self.lowered = 0
        self._ident = 0
        # Custom assertion helpers defined on the TestCase are inlined by
        # SelfRewrite, not lowered here -- `lower.build` has no case for them and
        # would raise.
        self.own_helpers = own_helpers

    def _next(self) -> int:
        self._ident += 1
        return self._ident

    def rewrite_block(self, body: list[ast.stmt]) -> list[ast.stmt]:
        out = []
        for stmt in body:
            call = lower.is_assertion_stmt(stmt)
            if call is not None and call.func.attr in self.own_helpers:
                call = None
            if call is not None:
                if call.func.attr in lower.WARNS:
                    block = lower.build_warns_block(call, self._next())
                    if block is None:
                        raise ValueError(
                            f"unlowerable {call.func.attr} at line {stmt.lineno}")
                    out.extend(block)
                    self.lowered += 1
                    continue
                if call.func.attr in lower.RAISES:
                    block = lower.build_raises_block(call, self._next())
                    if block is None:
                        raise ValueError(
                            f"unlowerable {call.func.attr} at line {stmt.lineno}")
                    out.extend(block)
                    self.lowered += 1
                    continue
                cond = lower.build(call)
                if cond is None:
                    raise ValueError(f"unlowerable assertion at line {stmt.lineno}")
                out.append(ast.Assert(test=cond, msg=None))
                self.lowered += 1
                continue
            if call is None and isinstance(stmt, ast.Expr):
                c = stmt.value
                if (isinstance(c, ast.Call) and isinstance(c.func, ast.Attribute)
                        and isinstance(c.func.value, ast.Name)
                        and c.func.value.id == "self"):
                    block = lower.build_fail(c)
                    if block is not None:
                        out.extend(block)
                        self.lowered += 1
                        continue
            if isinstance(stmt, ast.With) and len(stmt.items) == 1:
                # the body has to be lowered before it is folded into the try
                inner = self.rewrite_block(stmt.body)
                if lower.is_subtest(stmt.items[0]):
                    # subTest only groups; the body runs either way
                    out.extend(inner)
                    continue
                ident = self._next()
                block = lower.build_warns_with(stmt.items[0], inner, ident)
                if block is not None:
                    out.extend(block)
                    self.lowered += 1
                    continue
                block = lower.build_raises_with(stmt.items[0], inner, ident)
                if block is not None:
                    out.extend(block)
                    self.lowered += 1
                    # `with ... as cm` binds the exception for the statements that
                    # FOLLOW the block, so they are rewritten here: `cm.exception`
                    # becomes the local the scaffold kept it in. The rewrite has to
                    # happen on the rest of this block, which is why it lives in the
                    # statement loop rather than in lower.py.
                    cm = lower.with_binding(stmt.items[0])
                    if cm is not None:
                        rest = _rewrite_cm(body[body.index(stmt) + 1:], cm,
                                           lower.exc_var(ident))
                        out.extend(self.rewrite_block(rest))
                        return out
                    continue
                stmt.body = inner
                out.append(stmt)
                continue
            out.append(self.visit(stmt))
        return out

    def generic_visit(self, node):
        for field in ("body", "orelse", "finalbody"):
            if isinstance(getattr(node, field, None), list):
                setattr(node, field, self.rewrite_block(getattr(node, field)))
        for h in getattr(node, "handlers", []) or []:
            h.body = self.rewrite_block(h.body)
        return node


class _RenameReceiver(ast.NodeTransformer):
    """Rename one method's receiver, leaving nested scopes that bind their own alone."""

    def __init__(self, old: str) -> None:
        self.old = old
        self.shadowed = False

    def _scope(self, n, args):
        names = {a.arg for a in args.args + args.posonlyargs + args.kwonlyargs}
        prev = self.shadowed
        self.shadowed = self.shadowed or bool(names & {"self", self.old})
        self.generic_visit(n)
        self.shadowed = prev
        return n

    def visit_FunctionDef(self, n):
        return self._scope(n, n.args)

    visit_AsyncFunctionDef = visit_FunctionDef

    def visit_Lambda(self, n):
        return self._scope(n, n.args)

    def visit_Name(self, n):
        if n.id == self.old and not self.shadowed:
            n.id = "self"
        return n


def normalise_source(source: str) -> str:
    """Rename any method receiver that is not called `self` or `cls`.

    Everything downstream -- the selector's assertion detection, the lowering, the
    `self.x` rewrite -- matches the literal name `self`, in more than half a dozen
    places. A method is free to call its first parameter whatever it likes, and
    test_augassign.testCustomMethods2 calls it `test_self`: its assertions were
    therefore never recognised, never lowered, and the generated program raised
    `NameError: name 'test_self' is not defined`. Normalising once here is cheaper and
    less error-prone than threading the receiver's name through every match.

    The source is returned UNCHANGED unless some method actually needs the rename, so
    the other 53 files in the manifest are not reformatted by the round trip.
    """
    tree = ast.parse(source)
    touched = False
    for cls in [n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)]:
        for fn in cls.body:
            if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            decorators = {d.id for d in fn.decorator_list if isinstance(d, ast.Name)}
            if decorators & {"staticmethod", "classmethod"}:
                continue
            args = fn.args.posonlyargs + fn.args.args
            if not args or args[0].arg in ("self", "cls"):
                continue
            old = args[0].arg
            args[0].arg = "self"
            rename = _RenameReceiver(old)
            fn.body = [rename.visit(st) for st in fn.body]
            touched = True
    if not touched:
        return source
    return ast.unparse(ast.fix_missing_locations(tree))


def find_class(tree: ast.Module, method: dict) -> ast.ClassDef:
    """The TestCase class holding `method`. Takes a parsed tree, not source: parsing
    each corpus file three times per method cost real time on files like test_descr."""
    for c in ast.walk(tree):
        if isinstance(c, ast.ClassDef) and c.name == method["cls"]:
            return c
    raise KeyError(method["cls"])


def find_method(tree: ast.Module, method: dict) -> ast.FunctionDef:
    for x in find_class(tree, method).body:
        if isinstance(x, ast.FunctionDef) and x.name == method["method"]:
            return x
    raise KeyError(f"{method['cls']}.{method['method']}")


def module_defs(tree: ast.Module) -> dict[str, ast.stmt]:
    """Module-level name -> the statement that binds it, for the prelude."""
    out: dict[str, ast.stmt] = {}
    for s in tree.body:
        if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            out[s.name] = s
        elif isinstance(s, ast.Import):
            for a in s.names:
                out[a.asname or a.name.split(".")[0]] = s
        elif isinstance(s, ast.ImportFrom):
            for a in s.names:
                out[a.asname or a.name] = s
        elif isinstance(s, ast.Assign):
            # STORE context only. A target like `d[k] = v` or `obj.attr = v` also
            # contains LOAD names (`d`, `k`, `obj`); registering those as bound by this
            # statement made the later write clobber the earlier `d = {}`, so the
            # prelude emitted `d[k] = v` and left `d` undefined.
            for n in _bound_names(s.targets):
                out[n] = s
        elif isinstance(s, ast.AnnAssign) and isinstance(s.target, ast.Name):
            out[s.target.id] = s
    return out


def _bound_names(targets: list[ast.expr]) -> set[str]:
    """The names an assignment's targets actually BIND."""
    return {n.id for t in targets for n in ast.walk(t)
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)}


def _names(node) -> set[str]:
    return {n.id for n in ast.walk(node) if isinstance(n, ast.Name)}


def _uses_re(node) -> bool:
    return any(isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name)
               and n.value.id == "re" and n.attr == "search"
               for n in ast.walk(node))


def _imports_re(st: ast.stmt) -> bool:
    return isinstance(st, ast.Import) and any(a.name == "re" for a in st.names)


def _uses_warnings(node) -> bool:
    return any(isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name)
               and n.value.id == "warnings"
               and n.attr in ("catch_warnings", "simplefilter")
               for n in ast.walk(node))


def _imports_warnings(st: ast.stmt) -> bool:
    return (isinstance(st, ast.Import)
            and any(a.name == "warnings" for a in st.names))


def _is_main_guard(st: ast.stmt) -> bool:
    return (isinstance(st, ast.If) and isinstance(st.test, ast.Compare)
            and isinstance(st.test.left, ast.Name) and st.test.left.id == "__name__")


def _is_docstring(st: ast.stmt) -> bool:
    return isinstance(st, ast.Expr) and isinstance(st.value, ast.Constant)


def _is_mutator(st: ast.stmt) -> bool:
    """A module-level statement that can change a definition rather than make one.

    `module_defs` only indexes statements that BIND a name, so anything that mutates
    one afterwards was dropped. test_class.py builds its fixture that way --
    `d = {}` then `exec(statictests, globals(), d)` then a `for` loop of `exec`, and
    only then `AllTests = type('AllTests', (object,), d)` -- so `AllTests` reached the
    generated program with none of its operators and all five of its methods failed
    with `TypeError: unsupported operand type(s) for +: 'AllTests' and 'int'`.

    The `__main__` guard is excluded by name: it calls `unittest.main()`, which would
    run the entire file as a side effect of the prelude.
    """
    if _is_main_guard(st) or _is_docstring(st):
        return False
    # An assignment that binds no name is a mutation of something else:
    # `d[k] = v`, `obj.attr = v`. `module_defs` cannot index it, so without this the
    # statement would be dropped entirely.
    if isinstance(st, ast.Assign):
        return not _bound_names(st.targets)
    if isinstance(st, ast.AnnAssign):
        return not _bound_names([st.target])
    return isinstance(st, (ast.Expr, ast.AugAssign, ast.For, ast.AsyncFor, ast.While,
                           ast.If, ast.With, ast.AsyncWith, ast.Try))


def prelude_for(tree: ast.Module, seeds: list[ast.AST]) -> list[ast.stmt]:
    """The transitive closure of module-level definitions `seeds` need, in file order.

    A definition can need others -- a helper class referring to a constant, a function
    calling another -- so the closure is taken to a fixed point rather than one level
    deep. Statements that MUTATE a name already in the closure are pulled in too (see
    `_is_mutator`), and since a mutator can itself reference new names the two kinds
    are closed over together.
    """
    defs = module_defs(tree)
    order = {id(s): i for i, s in enumerate(tree.body)}
    chosen: dict[int, ast.stmt] = {}
    provided: set[str] = set()
    frontier: set[str] = set()
    for s in seeds:
        frontier |= _names(s)
    mutators = [s for s in tree.body if _is_mutator(s)]

    def close_defs() -> None:
        while frontier:
            name = frontier.pop()
            stmt = defs.get(name)
            if stmt is None or id(stmt) in chosen:
                continue
            chosen[id(stmt)] = stmt
            provided.add(name)
            # a class's own name is bound by itself; do not recurse forever
            frontier.update(_names(stmt) - {name})

    close_defs()
    changed = True
    while changed:
        changed = False
        for st in mutators:
            if id(st) in chosen:
                continue
            if _names(st) & provided:
                chosen[id(st)] = st
                frontier |= _names(st)
                changed = True
        close_defs()
    return [s for _, s in sorted(((order.get(id(s), 0), s)
                                 for s in chosen.values()), key=lambda kv: kv[0])]










DYNAMIC_BUILTINS = frozenset({"exec", "eval", "compile", "globals", "locals",
                              "vars"})


def _check_compiles(module: ast.Module) -> None:
    """Last line of defence: a generated program must at least be a valid program.

    The rewrites are scope-sensitive enough that one can produce something Python
    refuses to compile -- an illegal `nonlocal`, for instance. Recording that as a skip
    keeps it out of the results, where it would otherwise be indistinguishable from the
    front end rejecting the input.
    """
    try:
        compile(module, "<cpython_oracle>", "exec")
    except SyntaxError as e:
        raise ValueError(f"generated program does not compile: {e.msg}") from None


def _check_no_prelude_exec(prelude: list[ast.stmt]) -> None:
    """The out-of-scope judgement on `exec`/`eval` covers the prelude, not just the body.

    `_Reject` inspects the METHOD, so a file that builds its fixtures dynamically at
    module level slips past it. test_class.py assembles `AllTests` by `exec`-ing a
    template string, and every one of its five selected methods then failed with
    `TypeError: unsupported operand type(s) for +: 'AllTests' and 'int'` -- the class
    reached the generated program without any of its operators.
    """
    for st in prelude:
        for n in ast.walk(st):
            if (isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                    and n.func.id in DYNAMIC_BUILTINS):
                raise ValueError(f"prelude needs `{n.func.id}`")


_INST = "_cpython_oracle_case"


def base_name(b: ast.expr) -> str | None:
    """`Foo` or `mod.Foo` as written, or None for anything more complex."""
    if isinstance(b, ast.Name):
        return b.id
    if isinstance(b, ast.Attribute):
        inner = base_name(b.value)
        return f"{inner}.{b.attr}" if inner else None
    return None


# Bases that supply only the unittest framework. They are dropped: every assertion is
# lowered, so nothing inherited from them is needed, and emitting them would ask the
# front end to translate unittest itself.
_FRAMEWORK_BASES = frozenset({
    "unittest.TestCase", "TestCase", "unittest.IsolatedAsyncioTestCase",
    "IsolatedAsyncioTestCase", "object",
})


def classify_bases(cls: ast.ClassDef, tree: ast.Module
                   ) -> tuple[list[str], list[ast.ClassDef]]:
    """(base names to keep, their definitions).

    A base defined in the same file is kept -- that is the point of this mode, since
    the inherited-helper rejection was the largest group the hoisting design could not
    reach. Any other base is DROPPED rather than treated as disqualifying: emitting it
    would mean translating `test.support` or another library module, but rejecting the
    class outright cost 283 methods, far more than the mixins actually supply. Most are
    assertion mixins (`ExtraAssertions`, `FloatsAreIdenticalMixin`) that the method
    under test never touches.

    Dropping is safe rather than silent: if the method does call something the dropped
    base supplied, the generated program raises AttributeError, and runner.py's
    comparison against the original marks it `loweringBroken` instead of scoring it.
    """
    by_name = {c.name: c for c in tree.body if isinstance(c, ast.ClassDef)}
    keep: list[str] = []
    defs: list[ast.ClassDef] = []
    for b in cls.bases:
        name = base_name(b)
        if name is None or name in _FRAMEWORK_BASES:
            continue
        local = by_name.get(name)
        if local is None:
            continue
        keep.append(name)
        defs.append(local)
    return keep, defs


def method_table(cls: ast.ClassDef, bases: list[ast.ClassDef]
                 ) -> dict[str, ast.FunctionDef]:
    """Methods visible on `cls`, with the class's own winning over a base's."""
    table: dict[str, ast.FunctionDef] = {}
    for src in [*bases, cls]:
        for x in src.body:
            if isinstance(x, ast.FunctionDef):
                table[x.name] = x
    return table


def needed_methods(fn: ast.FunctionDef, table: dict[str, ast.FunctionDef],
                   seeds: list[ast.FunctionDef]) -> set[str]:
    """Transitive closure of `self.X()` method references, from `fn` and the fixtures.

    Anything reached through `self` that is NOT a method in `table` is left alone: it
    is either an attribute the fixture sets or an attribute the program will fail on,
    and in this mode the program is allowed to fail on it honestly rather than being
    rejected for it.
    """
    out: set[str] = set()
    frontier = [fn, *seeds]
    while frontier:
        node = frontier.pop()
        for n in ast.walk(node):
            if (isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name)
                    and n.value.id in ("self", "cls") and n.attr in table
                    and n.attr not in out):
                out.add(n.attr)
                frontier.append(table[n.attr])
    return out


def _lower_method(fn: ast.FunctionDef, own_helpers: set[str]) -> tuple[ast.FunctionDef, int]:
    """Lower the assertions in one method, in place, inside the class."""
    low = _Lower(own_helpers)
    out = copy.deepcopy(fn)
    out.body = low.rewrite_block(out.body)
    # A leading run of asserts at the top of a function body is promoted into that
    # function's `requires` by V2 (splitPreconditions), which would stop them being
    # statements to execute. A leading `pass` defeats it.
    out.body = [ast.Pass()] + out.body
    out.decorator_list = []
    return out, low.lowered


def _check_no_surviving_assertions(nodes: list[ast.AST]) -> None:
    """No `self.assertX` may reach the emitted program.

    The lowering rewrites assertion STATEMENTS. An assertion used anywhere else -- as a
    value, passed as a callable, inside a `return` -- is left alone, and since the
    unittest base is dropped the emitted class has no such method: the program dies
    with `AttributeError: 'T' object has no attribute 'assertEqual'`. That was 20
    methods, scored as `loweringBroken` where no verdict is drawn; rejecting them states
    the reason instead.
    """
    for node in nodes:
        for n in ast.walk(node):
            if (isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name)
                    and n.value.id in ("self", "cls")
                    and (n.attr.startswith("assert") or n.attr in lower.LOWERABLE_SELF)):
                raise ValueError(f"unlowered `self.{n.attr}` survives in the class")


def generate(source: str, method: dict) -> tuple[str, int]:
    """Return (program source, number of assertions lowered)."""
    tree = ast.parse(source)
    cls = find_class(tree, method)
    fn = find_method(tree, method)

    base_names, base_defs = classify_bases(cls, tree)

    table = method_table(cls, base_defs)
    setup = table.get("setUp")
    setup_cls = table.get("setUpClass")
    fixtures = [f for f in (setup, setup_cls) if f is not None]
    helpers = needed_methods(fn, table, fixtures) - {fn.name, "setUp", "setUpClass"}

    # Which methods go in the emitted class: the test, the fixtures, the helper
    # closure. Everything else is dropped -- see the module docstring on pruning.
    keep_names = {fn.name} | helpers | {f.name for f in fixtures}
    n_lowered = 0
    members: list[ast.stmt] = []

    # Class-body attributes stay class attributes, which is what they were. The
    # An earlier design had to turn these into `self_X` locals and hoist nested classes.
    for st in cls.body:
        if isinstance(st, (ast.Assign, ast.AnnAssign)):
            members.append(copy.deepcopy(st))
        elif isinstance(st, ast.ClassDef):
            members.append(copy.deepcopy(st))

    for name in sorted(keep_names):
        src_fn = table.get(name)
        if src_fn is None:
            raise ValueError(f"method {name!r} not found on the class or its bases")
        lowered, n = _lower_method(src_fn, helpers)
        members.append(lowered)
        n_lowered += n

    if not members:
        members = [ast.Pass()]

    emitted = ast.ClassDef(name=cls.name, bases=[ast.Name(id=b, ctx=ast.Load())
                                                 for b in base_names],
                           keywords=[], body=members, decorator_list=[],
                           type_params=[])

    # A base is emitted whole, so ITS methods need lowering too. An un-lowered
    # `self.assertX` anywhere in a base -- even in a method the test never calls -- has
    # no method to dispatch to once `unittest.TestCase` is dropped, and it would trip
    # the surviving-assertion check and skip the method.
    base_emitted = []
    for b in base_defs:
        bc = copy.deepcopy(b)
        bc.body = [(_lower_method(x, helpers)[0]
                    if isinstance(x, ast.FunctionDef) else x) for x in bc.body]
        base_emitted.append(bc)

    driver: list[ast.stmt] = []
    if setup_cls is not None:
        driver.append(ast.Expr(ast.Call(
            func=ast.Attribute(value=ast.Name(id=cls.name, ctx=ast.Load()),
                               attr="setUpClass", ctx=ast.Load()),
            args=[], keywords=[])))
    driver.append(ast.Assign(
        targets=[ast.Name(id=_INST, ctx=ast.Store())],
        value=ast.Call(func=ast.Name(id=cls.name, ctx=ast.Load()), args=[],
                       keywords=[])))
    if setup is not None:
        driver.append(ast.Expr(ast.Call(
            func=ast.Attribute(value=ast.Name(id=_INST, ctx=ast.Load()),
                               attr="setUp", ctx=ast.Load()),
            args=[], keywords=[])))
    driver.append(ast.Expr(ast.Call(
        func=ast.Attribute(value=ast.Name(id=_INST, ctx=ast.Load()),
                           attr=fn.name, ctx=ast.Load()),
        args=[], keywords=[])))

    seeds = base_emitted + [emitted]
    module_setup: list[ast.stmt] = []
    for st in tree.body:
        if isinstance(st, ast.FunctionDef) and st.name == "setUpModule":
            module_setup += [copy.deepcopy(x) for x in st.body]
    stars = [copy.deepcopy(st) for st in tree.body
             if isinstance(st, ast.ImportFrom)
             and any(a.name == "*" for a in st.names)]

    prelude = prelude_for(tree, seeds + module_setup)
    # The class itself is in the prelude's closure (it is a module-level definition);
    # emitting it twice would shadow the pruned copy with the original.
    drop = {cls.name, *base_names}
    prelude = [st for st in prelude
               if not (isinstance(st, ast.ClassDef) and st.name in drop)]
    prelude = stars + prelude + module_setup
    # `assertRaisesRegex` / `assertRegex` lower to `re.search`, which the file itself
    # need not have imported -- added only when a lowering used it, since an
    # unconditional import would change what the front end is asked to translate in
    # every other program. Omitting it was 111 `loweringBroken` methods, all dying with
    # `NameError: name 're' is not defined`.
    emitted_nodes = base_emitted + [emitted]
    _check_no_surviving_assertions(emitted_nodes)
    if any(_uses_re(n) for n in emitted_nodes) and not any(_imports_re(st)
                                                          for st in prelude):
        prelude = [ast.Import(names=[ast.alias(name="re", asname=None)])] + prelude
    # `assertWarns` lowers to `warnings.catch_warnings`, on the same terms.
    if any(_uses_warnings(n) for n in emitted_nodes) and not any(
            _imports_warnings(st) for st in prelude):
        prelude = [ast.Import(names=[ast.alias(name="warnings",
                                               asname=None)])] + prelude

    module = ast.fix_missing_locations(ast.Module(
        body=prelude + base_emitted + [emitted] + driver, type_ignores=[]))
    _check_compiles(module)
    _check_no_prelude_exec(prelude)
    return ast.unparse(module), n_lowered

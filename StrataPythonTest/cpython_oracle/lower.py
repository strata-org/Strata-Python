"""Lower a unittest assertion call to the plain Python `assert` it means.

`self.assertEqual(a, b)` becomes `assert a == b`. This is the whole reason the suite
can say anything: the lowered form IS the assertion's semantics, expressed in the
Python the front end already analyses, so there is no model to get wrong.

An earlier version routed assertions through a PySpec stub whose bare `assert`
becomes a precondition. That works, but the PySpec assert-to-precondition translator
accepts far less than the program front end: it drops `<=`, `is` and `bool(x)`
("unsupported comparison" / "unsupported call"), which forced assertLessEqual,
assertIs and assertTrue out of the modelled set. All three are fine as ordinary
program asserts, so lowering here instead roughly quintuples what the suite reaches
and removes the risk of approximating an assertion.

Only assertions whose meaning is EXACTLY a Python expression are lowered. The
`assertXEqual` family (assertListEqual, assertMultiLineEqual, ...) is excluded
because unittest also checks the operands' types, so `a == b` would be weaker, and a
weaker obligation could let the front end pass what CPython fails.

assertAlmostEqual and assertRaisesRegex were excluded on the same grounds and are not
any more: both are specified exactly enough to reproduce -- the first as
`a == b or round(abs(b - a), places) == 0` (or `abs(a - b) <= delta`), the second as
`re.search(pattern, str(exc))` inside the handler. Together they are the two most
common assertions the suite could not reach.
"""
from __future__ import annotations

import ast

# assertion name -> (arity, builder from the call's positional args)
_BINCMP = {
    "assertEqual": ast.Eq, "assertNotEqual": ast.NotEq,
    "assertIs": ast.Is, "assertIsNot": ast.IsNot,
    "assertIn": ast.In, "assertNotIn": ast.NotIn,
    "assertLess": ast.Lt, "assertLessEqual": ast.LtE,
    "assertGreater": ast.Gt, "assertGreaterEqual": ast.GtE,
}


def _cmp(op, a, b):
    return ast.Compare(left=a, ops=[op()], comparators=[b])


def _fn(name: str, args: list[ast.expr]) -> ast.Call:
    return ast.Call(func=ast.Name(id=name, ctx=ast.Load()), args=args, keywords=[])


def _abs(e: ast.expr) -> ast.Call:
    return _fn("abs", [e])


def _re_search(pattern: ast.expr, text: ast.expr) -> ast.Call:
    """`re.search(pattern, text)`. prepare.py adds the import when this appears."""
    return ast.Call(func=ast.Attribute(value=ast.Name(id="re", ctx=ast.Load()),
                                       attr="search", ctx=ast.Load()),
                    args=[pattern, text], keywords=[])


def _is_none(e: ast.expr | None) -> bool:
    return e is None or (isinstance(e, ast.Constant) and e.value is None)


def _almost(name: str, call: ast.Call) -> ast.expr | None:
    """`assertAlmostEqual` / `assertNotAlmostEqual`, honouring `places` and `delta`.

    unittest's signature is
    `assertAlmostEqual(first, second, places=None, msg=None, delta=None)`, so the THIRD
    POSITIONAL argument is `places` -- not `msg`, as it is for every other assertion
    lowered here. Reading it as `msg` and lowering with the default tolerance of 7
    places asserts something different from, and weaker than, what the test says, which
    is the one failure mode this module exists to avoid.

    Both `places` and `delta` is a TypeError in unittest, so it is refused rather than
    resolved one way or the other.
    """
    args = list(call.args)
    if any(k.arg is None for k in call.keywords):          # **kwargs
        return None
    kw = {k.arg: k.value for k in call.keywords}
    if any(a not in ("msg", "places", "delta") for a in kw):
        return None
    if not 2 <= len(args) <= 3:
        return None
    places, delta = kw.get("places"), kw.get("delta")
    if len(args) == 3:
        if places is not None:
            return None                                    # positional and keyword
        places = args[2]
    if _is_none(places):
        places = None
    if _is_none(delta):
        delta = None
    if places is not None and delta is not None:
        return None
    if delta is not None:
        near = _cmp(ast.LtE,
                    _abs(ast.BinOp(left=args[0], op=ast.Sub(), right=args[1])), delta)
    else:
        diff = _abs(ast.BinOp(left=args[1], op=ast.Sub(), right=args[0]))
        near = _cmp(ast.Eq, _fn("round", [diff, places or ast.Constant(value=7)]),
                    ast.Constant(value=0))
    cond = ast.BoolOp(op=ast.Or(), values=[_cmp(ast.Eq, args[0], args[1]), near])
    if name == "assertAlmostEqual":
        return cond
    return ast.UnaryOp(op=ast.Not(), operand=cond)


def build(call: ast.Call) -> ast.expr | None:
    """The condition `call` asserts, or None if it is not exactly lowerable."""
    name = call.func.attr
    args = call.args
    # assertAlmostEqual is the one assertion whose extra arguments are not `msg`, so it
    # is handled before the msg-only guard below would reject them.
    if name in ("assertAlmostEqual", "assertNotAlmostEqual"):
        return _almost(name, call)
    # keyword args are only ever `msg=`; a positional msg is the arity+1 case
    if any(k.arg != "msg" for k in call.keywords):
        return None

    if name in _BINCMP:
        if len(args) not in (2, 3):     # 3rd positional is msg
            return None
        return _cmp(_BINCMP[name], args[0], args[1])
    if name == "assertTrue":
        if len(args) not in (1, 2):
            return None
        return args[0]
    if name == "assertFalse":
        if len(args) not in (1, 2):
            return None
        return ast.UnaryOp(op=ast.Not(), operand=args[0])
    if name == "assertIsNone":
        if len(args) not in (1, 2):
            return None
        return _cmp(ast.Is, args[0], ast.Constant(value=None))
    if name == "assertIsNotNone":
        if len(args) not in (1, 2):
            return None
        return _cmp(ast.IsNot, args[0], ast.Constant(value=None))
    if name in ("assertRegex", "assertNotRegex"):
        # unittest compiles a str pattern and calls `.search(text)`; `re.search`
        # accepts an already-compiled pattern too, so one form covers both.
        if len(args) not in (2, 3):
            return None
        found = _cmp(ast.IsNot, _re_search(args[1], args[0]),
                     ast.Constant(value=None))
        if name == "assertRegex":
            return found
        return ast.UnaryOp(op=ast.Not(), operand=found)
    if name in ("assertHasAttr", "assertNotHasAttr"):
        if len(args) not in (2, 3):
            return None
        has = _fn("hasattr", [args[0], args[1]])
        if name == "assertHasAttr":
            return has
        return ast.UnaryOp(op=ast.Not(), operand=has)
    if name in ("assertIsInstance", "assertNotIsInstance"):
        if len(args) not in (2, 3):
            return None
        c = ast.Call(func=ast.Name(id="isinstance", ctx=ast.Load()),
                     args=[args[0], args[1]], keywords=[])
        return c if name == "assertIsInstance" else ast.UnaryOp(op=ast.Not(), operand=c)
    return None


# unittest methods that are not assertions but do lower exactly.
#
#   self.fail(msg)          -> assert False      (fail() raises unconditionally)
#   with self.subTest(..):  -> the body, inlined
#
# subTest only groups: the body runs either way, and its effect is to let a failing
# body be reported without aborting the rest of the method. Every method this suite
# selects passes under CPython, so no subTest body fails and inlining is exact. The
# generated-program check in runner.py is what would catch it if that stopped holding.
LOWERABLE_SELF = frozenset({"fail", "subTest"})


def build_fail(call: ast.Call) -> list[ast.stmt] | None:
    """Lower `self.fail(...)` to `assert False`."""
    if call.func.attr != "fail":
        return None
    return [ast.Assert(test=ast.Constant(value=False), msg=None)]


def is_subtest(item) -> bool:
    e = item.context_expr
    return (isinstance(e, ast.Call) and isinstance(e.func, ast.Attribute)
            and isinstance(e.func.value, ast.Name) and e.func.value.id == "self"
            and e.func.attr == "subTest")


_RAISED = "_cpython_oracle_raised"
_EXC = "_cpython_oracle_exc"


RAISES = frozenset({"assertRaises", "assertRaisesRegex"})
WARNS = frozenset({"assertWarns", "assertWarnsRegex"})

_WARNLOG = "_cpython_oracle_warn"


def warns_category(call: ast.Call) -> ast.expr | None:
    """The warning category `self.assertWarns*(W, ...)` expects, if lowerable."""
    if call.func.attr not in WARNS or not call.args:
        return None
    if any(k.arg is None for k in call.keywords):
        return None
    if call.func.attr == "assertWarnsRegex" and len(call.args) < 2:
        return None
    return call.args[0]


def warns_regex(call: ast.Call) -> ast.expr | None:
    """The message pattern `assertWarnsRegex` also requires."""
    return call.args[1] if call.func.attr == "assertWarnsRegex" else None


def build_warns(category: ast.expr, regex: ast.expr | None,
                body: list[ast.stmt], ident: int) -> list[ast.stmt]:
    """`with self.assertWarns(W): body` -> catch_warnings plus an assert.

    unittest requires at least one warning of the category, and `assertWarnsRegex`
    additionally matches its message, which is what this asserts. `simplefilter('always')`
    matches unittest, which resets `__warningregistry__` so a warning already issued once
    is not swallowed.
    """
    log = f"{_WARNLOG}{ident}"
    item = ast.Name(id=f"{log}_w", ctx=ast.Load())
    hit: ast.expr = _fn("issubclass", [ast.Attribute(value=item, attr="category",
                                                     ctx=ast.Load()), category])
    if regex is not None:
        hit = ast.BoolOp(op=ast.And(), values=[hit, _cmp(
            ast.IsNot,
            _re_search(regex, _fn("str", [ast.Attribute(value=item, attr="message",
                                                        ctx=ast.Load())])),
            ast.Constant(value=None))])
    any_call = ast.Call(
        func=ast.Name(id="any", ctx=ast.Load()),
        args=[ast.GeneratorExp(elt=hit, generators=[ast.comprehension(
            target=ast.Name(id=f"{log}_w", ctx=ast.Store()),
            iter=ast.Name(id=log, ctx=ast.Load()), ifs=[], is_async=0)])],
        keywords=[])
    catch = ast.withitem(
        context_expr=ast.Call(
            func=ast.Attribute(value=ast.Name(id="warnings", ctx=ast.Load()),
                               attr="catch_warnings", ctx=ast.Load()),
            args=[], keywords=[ast.keyword(arg="record",
                                           value=ast.Constant(value=True))]),
        optional_vars=ast.Name(id=log, ctx=ast.Store()))
    simple = ast.Expr(ast.Call(
        func=ast.Attribute(value=ast.Name(id="warnings", ctx=ast.Load()),
                           attr="simplefilter", ctx=ast.Load()),
        args=[ast.Constant(value="always")], keywords=[]))
    return [ast.With(items=[catch], body=[simple] + list(body)),
            ast.Assert(test=any_call, msg=None)]


def build_warns_with(item, body: list[ast.stmt], ident: int) -> list[ast.stmt] | None:
    """`with self.assertWarns(W): body`, or None if not lowerable."""
    call = item.context_expr
    if not (isinstance(call, ast.Call) and isinstance(call.func, ast.Attribute)
            and isinstance(call.func.value, ast.Name) and call.func.value.id == "self"):
        return None
    cat = warns_category(call)
    if cat is None or item.optional_vars is not None:
        return None                       # `as cm` exposes warning/filename/lineno
    if any(k.arg != "msg" for k in call.keywords):
        return None
    return build_warns(cat, warns_regex(call), body, ident)


def build_warns_block(call: ast.Call, ident: int) -> list[ast.stmt] | None:
    """`self.assertWarns(W, fn, *args)`, or None if not lowerable."""
    cat = warns_category(call)
    if cat is None:
        return None
    regex = warns_regex(call)
    rest = call.args[2:] if regex is not None else call.args[1:]
    if not rest:
        return None
    fwd = [k for k in call.keywords if k.arg != "msg"]
    inner = ast.Expr(ast.Call(func=rest[0], args=list(rest[1:]), keywords=fwd))
    return build_warns(cat, regex, [inner], ident)


def raises_exception(call: ast.Call) -> ast.expr | None:
    """The exception type `self.assertRaises*(E, ...)` expects, if it is lowerable.

    Keywords other than `msg` are NOT disqualifying: unittest pops `msg` and forwards
    everything else to the callable, so
    `assertRaises(OverflowError, (256).to_bytes, 1, 'big', signed=False)` means
    `(256).to_bytes(1, 'big', signed=False)`. Treating them as arguments to assertRaises
    itself refused 45 call sites. `**kwargs` is still refused, since the callable's
    keywords cannot then be named.
    """
    if call.func.attr not in RAISES or not call.args:
        return None
    if any(k.arg is None for k in call.keywords):
        return None
    if call.func.attr == "assertRaisesRegex" and len(call.args) < 2:
        return None
    return call.args[0]


def raises_regex(call: ast.Call) -> ast.expr | None:
    """The message pattern `assertRaisesRegex` also requires, or None for plain form.

    Dropping the pattern would make the obligation WEAKER than the assertion, so it is
    carried through instead: unittest checks `expected_regex.search(str(exc))`, which
    is exactly what the generated handler asserts. That check was the only reason this
    form was refused, and it is the single most common assertion in the corpus at 233
    occurrences.
    """
    if call.func.attr != "assertRaisesRegex":
        return None
    return call.args[1]


def build_raises_block(call: ast.Call, ident: int) -> list[ast.stmt] | None:
    """Lower `self.assertRaises(E, fn, *args)` to try/except plus an assert.

    Only the CALLABLE form is handled here; the context-manager form is handled by
    `build_raises_with` because it carries the body with it.

        _raised = False
        try:
            fn(*args)
        except E:
            _raised = True
        assert _raised

    `except E` matches subclasses, which is exactly what unittest does, so the
    lowering is the assertion rather than an approximation of it.
    """
    exc = raises_exception(call)
    if exc is None:
        return None
    regex = raises_regex(call)
    rest = call.args[2:] if regex is not None else call.args[1:]
    if not rest:
        return None
    # Everything but `msg` belongs to the callable -- see `raises_exception`.
    fwd = [k for k in call.keywords if k.arg != "msg"]
    inner = ast.Expr(ast.Call(func=rest[0], args=list(rest[1:]), keywords=fwd))
    return _raises_scaffold(exc, [inner], ident, regex)


def with_binding(item) -> str | None:
    """The name `with ... as cm` binds, if it binds a plain name."""
    v = item.optional_vars
    return v.id if isinstance(v, ast.Name) else None


def exc_var(ident: int) -> str:
    """The local the scaffold binds the caught exception to."""
    return f"{_EXC}{ident}"


# The only attribute of an `assertRaises` context manager this lowering can reproduce.
# unittest also exposes `cm.msg`, and the assertWarns manager has `warning`/`filename`/
# `lineno`; a test reaching for any of those is refused rather than approximated.
CM_ATTR = "exception"


def build_raises_with(item, body: list[ast.stmt], ident: int) -> list[ast.stmt] | None:
    """Lower `with self.assertRaises(E): body` to try/except plus an assert.

    `with ... as cm` is supported: the caught exception is bound to a local, and the
    caller rewrites `cm.exception` in the statements that follow to name it. Without
    that rewrite the assertions made about `cm.exception` would be silently lost.
    """
    call = item.context_expr
    if not (isinstance(call, ast.Call) and isinstance(call.func, ast.Attribute)
            and isinstance(call.func.value, ast.Name) and call.func.value.id == "self"):
        return None
    exc = raises_exception(call)
    if exc is None:
        return None
    if any(k.arg != "msg" for k in call.keywords):
        return None            # a keyword here has no callable to go to
    if item.optional_vars is not None and with_binding(item) is None:
        return None                       # `as (a, b)` and the like
    bind = item.optional_vars is not None
    return _raises_scaffold(exc, body, ident, raises_regex(call), bind)


def _raises_scaffold(exc: ast.expr, body: list[ast.stmt], ident: int,
                     regex: ast.expr | None = None,
                     bind: bool = False) -> list[ast.stmt]:
    """`_raisedN = False; try: body; except E as e: ...; assert _raisedN`.

    When `bind` is set the caught exception is copied into `exc_var(ident)`, which
    outlives the handler -- `except E as e` unbinds `e` on exit, and the statements
    after a `with ... as cm` block still need it.
    """
    flag = f"{_RAISED}{ident}"
    caught = f"{_EXC}{ident}_caught"
    keep = exc_var(ident)
    need_name = bind or regex is not None

    handler: list[ast.stmt] = [
        ast.Assign(targets=[ast.Name(id=flag, ctx=ast.Store())],
                   value=ast.Constant(value=True))]
    if bind:
        handler.append(ast.Assign(targets=[ast.Name(id=keep, ctx=ast.Store())],
                                  value=ast.Name(id=caught, ctx=ast.Load())))
    if regex is not None:
        handler.append(ast.Assert(
            test=_cmp(ast.IsNot,
                      _re_search(regex, _fn("str", [ast.Name(id=caught, ctx=ast.Load())])),
                      ast.Constant(value=None)),
            msg=None))

    pre: list[ast.stmt] = [
        ast.Assign(targets=[ast.Name(id=flag, ctx=ast.Store())],
                   value=ast.Constant(value=False))]
    if bind:
        # Always bound, so the name exists even on the path where nothing was raised.
        pre.append(ast.Assign(targets=[ast.Name(id=keep, ctx=ast.Store())],
                              value=ast.Constant(value=None)))
    return pre + [
        ast.Try(body=list(body),
                handlers=[ast.ExceptHandler(type=exc,
                                            name=caught if need_name else None,
                                            body=handler)],
                orelse=[], finalbody=[]),
        ast.Assert(test=ast.Name(id=flag, ctx=ast.Load()), msg=None),
    ]


LOWERABLE = frozenset(
    set(WARNS)
    | set(_BINCMP)
    | {"assertTrue", "assertFalse", "assertIsNone", "assertIsNotNone",
       "assertIsInstance", "assertNotIsInstance",
       "assertAlmostEqual", "assertNotAlmostEqual",
       "assertRegex", "assertNotRegex", "assertHasAttr", "assertNotHasAttr"}
    | RAISES
)


def is_assertion_stmt(stmt: ast.stmt) -> ast.Call | None:
    """The `self.assertX(...)` call this statement consists of, if any."""
    if not isinstance(stmt, ast.Expr):
        return None
    c = stmt.value
    if (isinstance(c, ast.Call) and isinstance(c.func, ast.Attribute)
            and isinstance(c.func.value, ast.Name) and c.func.value.id == "self"
            and c.func.attr.startswith("assert")):
        return c
    return None


def condition_source(call: ast.Call) -> str | None:
    """`assert <cond>` source text for `call`, or None if not lowerable."""
    cond = build(call)
    if cond is None:
        return None
    return "assert " + ast.unparse(ast.fix_missing_locations(cond))

"""CPython's side of the invariant-run test: run a Python file as `__main__`, evaluate the loop
invariants whose ranks are given at each entry of their loop's head, and print the program's
output with one line per evaluation, then its outcome.

    python3.12 invariant_trace.py FILE.py RANKS [PARTS]

`RANKS` is a comma-separated list of ranks, possibly empty. An invariant's rank is its index
among all the module's `loop_invariant(lambda: P)` statements, ordered by the byte offset of the
start of `P`. The program's syntax tree is rewritten before it runs, so that the checks run
exactly at the head entries that `docs/PythonToDyn.md` §6.11 defines:

* `loop_invariant(lambda: P)` becomes `__pyhard_record__(rank, lambda: P)`, which records the
  lambda for the frame that runs it and calls nothing;
* `while test:` becomes `while __pyhard_check__(ranks) and (test):`;
* `for t in it:` becomes `for t in __pyhard_iter__(ranks, it):`, whose constructor calls
  `iter(it)` at once and whose `__next__` runs the checks, then `next`.

A marker's lambda `lambda: P` is recorded as `lambda: True if (P) else False`, so that `P` is
tested as `if P:` tests it. When `P` has an `OLD`, its parts read at entry are computed here, by
the rule of `docs/PythonToDyn.md` §6.11 (`old_parts`, written for this test, not taken from the
translator), and compared with the parts that `invRun` printed, given in the file `PARTS` (lines
`RANK<TAB>PART`); a difference exits with status 3. The function that holds the loop then
evaluates each part, at its first statement after its docstring, and records its value, or its
exception, or a `TypeError` when the value isn't an immutable scalar; in the recorded lambda,
each `OLD(part)` becomes a read of its record, which raises the recorded exception. A check calls the lambda of each given rank that the loop's markers
recorded, counts any exception as `False`, and prints `--- invariant <rank> <True|False>`. The
lambda of a rank that isn't given is never called. The helpers live in `builtins`, so the
program's globals don't change.

The output is `--- stdout <n>`, the n characters that the program printed (the invariant lines
among them), then `--- outcome` and `ok` or the exception's lines as `trace.py` prints them
(`raised <ExcType>: <str(exc)>`, then a `cause` or `context` line per link of its chain). Standard
error gets one line, `ranked <n>`: the number of marker statements ranked.
"""

import ast
import builtins
import copy
import importlib.util
import io
import os
import sys
import types

# trace.py's exception lines, so that both tracers print an exception the same way. Loading it
# also imports `pyhard` from `Python/pyhard/` and checks that it is that module.
_spec = importlib.util.spec_from_file_location(
    "_pyhard_trace", os.path.join(os.path.dirname(os.path.abspath(__file__)), "trace.py"))
TRACE = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(TRACE)


def marker_ranks(tree, source):
    """The rank of each marker statement, by the byte offset of the start of its `P`. A module
    that doesn't import the marker from `pyhard` at its top level has none: its
    `loop_invariant` is an ordinary name."""
    if not any(isinstance(s, ast.ImportFrom) and s.module == "pyhard" and s.level == 0
               and any(a.name == "loop_invariant" and a.asname is None for a in s.names)
               for s in tree.body):
        return {}
    lines = source.splitlines(keepends=True)  # bytes: col_offset counts UTF-8 bytes
    starts = [0]
    for line in lines:
        starts.append(starts[-1] + len(line))
    found = []
    for node in ast.walk(tree):
        if (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
                and isinstance(node.value.func, ast.Name)
                and node.value.func.id == "loop_invariant"
                and len(node.value.args) == 1 and isinstance(node.value.args[0], ast.Lambda)):
            body = node.value.args[0].body
            found.append((starts[body.lineno - 1] + body.col_offset, node))
    found.sort(key=lambda p: p[0])
    return {id(node): rank for rank, (_, node) in enumerate(found)}


# The exact types of an immutable scalar, as `py.isImmutableScalar` (Sem/Contracts/Ops.lean) has them.
SCALARS = (int, float, complex, bool, str, bytes, type(None))

DICT_VIEWS = ("items", "keys", "values")


def is_old(node):
    """Whether `node` is `OLD(e)`."""
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "OLD" and len(node.args) == 1 and not node.keywords)


def is_dict_view(node):
    """Whether `node` is `d.items()`, `d.keys()` or `d.values()`."""
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr in DICT_VIEWS and not node.args and not node.keywords)


def children(node):
    """The subexpressions that §6.11's rule looks into: a call's arguments (and its callee, when
    it isn't a name), a dict view's dict, the operands, an attribute's value, a subscript's value
    and index, a slice's bounds, and a quantifier's element, iterable and guards (not its
    target)."""
    if is_dict_view(node):
        return [node.func.value]
    if isinstance(node, ast.Call):
        return ([] if isinstance(node.func, ast.Name) else [node.func]) + list(node.args)
    if isinstance(node, ast.BinOp):
        return [node.left, node.right]
    if isinstance(node, ast.UnaryOp):
        return [node.operand]
    if isinstance(node, ast.Attribute):
        return [node.value]
    if isinstance(node, ast.BoolOp):
        return list(node.values)
    if isinstance(node, ast.Compare):
        return [node.left] + list(node.comparators)
    if isinstance(node, ast.IfExp):
        return [node.test, node.body, node.orelse]
    if isinstance(node, ast.Subscript):
        return [node.value, node.slice]
    if isinstance(node, ast.Slice):
        return [x for x in (node.lower, node.upper, node.step) if x is not None]
    if isinstance(node, ast.GeneratorExp) and len(node.generators) == 1:
        g = node.generators[0]
        return [node.elt, g.iter] + list(g.ifs)
    return []


def has_old(node):
    return is_old(node) or any(has_old(c) for c in children(node))


def reads_only_old(node):
    """Whether `node` reads no name outside its `OLD`s. A call's callee name, such as `len`, and a
    quantifier's target are no reads."""
    if is_old(node):
        return True
    if isinstance(node, ast.Name):
        return False
    if isinstance(node, ast.Call) and not isinstance(node.func, ast.Name) \
            and not is_dict_view(node):
        return False
    return all(reads_only_old(c) for c in children(node))


def may_be_part(node):
    """A slice, a dict view and a bare quantifier are never a part read at entry."""
    return not isinstance(node, (ast.Slice, ast.GeneratorExp)) and not is_dict_view(node)


def old_parts(node):
    """The parts that §6.11 reads at entry, in source order: each largest subexpression around
    an `OLD` that may be a part and reads no name outside its `OLD`s, as a node of `node`, with
    its `OLD`s still in it (`un_old` removes them)."""
    if not has_old(node):
        return []
    if is_old(node):
        return [node]
    if may_be_part(node) and reads_only_old(node):
        return [node]
    return [p for c in children(node) for p in old_parts(c)]


def un_old(node):
    """`node` with each `OLD(e)` replaced by `e`."""
    class UnOld(ast.NodeTransformer):
        def visit_Call(self, n):
            self.generic_visit(n)
            return n.args[0] if is_old(n) else n
    return UnOld().visit(copy.deepcopy(node))


def replace_parts(node, parts, record):
    """`node` with each of `parts` (nodes of `node`) replaced by a read of its record:
    `__pyhard_old__(record, k)`."""
    index = {id(p): k for k, p in enumerate(parts)}

    class Replace(ast.NodeTransformer):
        def visit(self, n):
            if id(n) in index:
                return ast.Call(ast.Name("__pyhard_old__", ast.Load()),
                                [ast.Name(record, ast.Load()), ast.Constant(index[id(n)])], [])
            return super().visit(n)
    return Replace().visit(node)


class Rewrite(ast.NodeTransformer):
    """Rewrites the marker statements and the loops that follow them."""

    def __init__(self, ranks, compared):
        self.ranks = ranks
        self.compared = compared
        # For each function being rewritten, the statements that record the parts at its entry.
        self.entries = []
        # The parts read at entry of each compared invariant with an `OLD`, as source text.
        self.parts = {}

    def visit_FunctionDef(self, node):
        self.entries.append([])
        node = self.generic_visit(node)
        snaps = self.entries.pop()
        first = 1 if (node.body and isinstance(node.body[0], ast.Expr)
                      and isinstance(node.body[0].value, ast.Constant)
                      and isinstance(node.body[0].value.value, str)) else 0
        node.body[first:first] = snaps
        return node

    visit_AsyncFunctionDef = visit_FunctionDef

    def olds(self, rank, f):
        """Rewrite the lambda `f` of invariant `rank` to read its parts from a record that the
        function's entry fills."""
        parts = old_parts(f.body)
        self.parts[rank] = [ast.dump(un_old(p)) for p in parts]
        if not parts or rank not in self.compared or not self.entries:
            return
        record = f"__pyhard_olds_{rank}__"
        lambdas = [ast.Lambda(ast.arguments([], [], None, [], [], None, []), un_old(p))
                   for p in parts]
        self.entries[-1].append(ast.Assign(
            [ast.Name(record, ast.Store())],
            ast.Call(ast.Name("__pyhard_snap__", ast.Load()),
                     [ast.Tuple(lambdas, ast.Load())], [])))
        f.body = replace_parts(f.body, parts, record)

    def body(self, stmts):
        out = []
        pending = []
        for s in stmts:
            s = self.visit(s)
            if isinstance(s, ast.Expr) and id(s) in self.ranks:
                rank = self.ranks[id(s)]
                pending.append(rank)
                # `True if (P) else False`: P is tested as `if P:` tests it, as the lowering does,
                # so a `__bool__` runs once for each operand that `and`, `or` or `not` tests.
                f = s.value.args[0]
                self.olds(rank, f)
                f.body = ast.IfExp(f.body, ast.Constant(True), ast.Constant(False))
                s.value = ast.Call(ast.Name("__pyhard_record__", ast.Load()),
                                   [ast.Constant(rank), f], [])
                out.append(s)
                continue
            if pending and isinstance(s, (ast.While, ast.For)):
                keys = ast.Tuple([ast.Constant(r) for r in pending], ast.Load())
                if isinstance(s, ast.While):
                    s.test = ast.BoolOp(ast.And(), [
                        ast.Call(ast.Name("__pyhard_check__", ast.Load()), [keys], []), s.test])
                else:
                    s.iter = ast.Call(ast.Name("__pyhard_iter__", ast.Load()), [keys, s.iter], [])
            pending = []
            out.append(s)
        return out

    def generic_visit(self, node):
        for field in ("body", "orelse", "finalbody"):
            value = getattr(node, field, None)
            if isinstance(value, list) and value and isinstance(value[0], ast.stmt):
                setattr(node, field, self.body(value))
        for field, value in ast.iter_fields(node):
            if field in ("body", "orelse", "finalbody") and isinstance(value, list) \
                    and value and isinstance(value[0], ast.stmt):
                continue
            if isinstance(value, list):
                setattr(node, field, [self.visit(v) if isinstance(v, ast.AST) else v
                                      for v in value])
            elif isinstance(value, ast.AST):
                setattr(node, field, self.visit(value))
        return node


def install(compared):
    """Put the three helpers in `builtins`. Recorded lambdas are kept per frame."""
    recorded = {}

    def record(rank, f):
        recorded[(id(sys._getframe(1)), rank)] = f

    def check_in(frame, keys):
        for rank in keys:
            if rank not in compared:
                continue
            f = recorded.get((id(frame), rank))
            if f is None:
                continue
            try:
                b = f()
            except BaseException:  # an exception inside P makes the invariant false
                b = False
            print(f"--- invariant {rank} {b}")
        return True

    def check(keys):
        return check_in(sys._getframe(1), keys)

    class Iter:
        def __init__(self, keys, it):
            self.frame = sys._getframe(1)
            self.keys = keys
            self.it = iter(it)

        def __iter__(self):
            return self

        def __next__(self):
            check_in(self.frame, self.keys)
            return next(self.it)

    def snap(fs):
        """Each part's value, or its exception, at the function's entry."""
        out = []
        for f in fs:
            try:
                v = f()
            except BaseException as e:  # an exception in a part makes the invariant false
                out.append((False, e))
                continue
            if type(v) in SCALARS:
                out.append((True, v))
            else:
                out.append((False, TypeError("a part read at entry that isn't an immutable scalar")))
        return out

    def old(rec, k):
        ok, v = rec[k]
        if ok:
            return v
        raise v

    builtins.__pyhard_record__ = record
    builtins.__pyhard_check__ = check
    builtins.__pyhard_iter__ = Iter
    builtins.__pyhard_snap__ = snap
    builtins.__pyhard_old__ = old


def check_parts(rewrite, parts_path):
    """Exit with status 3 unless the parts of each compared invariant are those in `parts_path`,
    which `invRun` printed from the translator's split."""
    theirs = {}
    if parts_path:
        with open(parts_path, encoding="utf-8") as f:
            for line in f.read().splitlines():
                rank, text = line.split("\t", 1)
                theirs.setdefault(int(rank), []).append(
                    ast.dump(ast.parse(text, mode="eval").body))
    for rank in sorted(rewrite.compared):
        ours = rewrite.parts.get(rank, [])
        if ours != theirs.get(rank, []):
            print(f"invariant_trace.py: the parts read at entry of invariant {rank} differ:\n"
                  f"  computed here: {ours}\n  invRun's:      {theirs.get(rank, [])}",
                  file=sys.stderr)
            sys.exit(3)


def main(path, ranks_text, parts_path):
    if sys.version_info[:2] != (3, 12):
        sys.exit(f"invariant_trace.py needs CPython 3.12, not {sys.version.split()[0]}")
    with open(path, "rb") as f:
        raw = f.read()
    source = importlib.util.decode_source(raw)
    tree = ast.parse(raw, path)
    compared = {int(r) for r in ranks_text.split(",") if r}
    ranks = marker_ranks(tree, raw)
    print(f"ranked {len(ranks)}", file=sys.stderr)
    rewrite = Rewrite(ranks, compared)
    tree = rewrite.visit(tree)
    check_parts(rewrite, parts_path)
    ast.fix_missing_locations(tree)
    code = compile(tree, path, "exec")
    del source
    sys.dont_write_bytecode = True
    install(compared)
    program_dir = os.path.dirname(os.path.realpath(path))
    os.chdir("/")
    module = types.ModuleType("__main__")
    out = io.StringIO()
    real = sys.stdout
    # As in `trace.py`, the program sees `python FILE.py`'s `sys.argv` and `sys.path[0]`.
    real_main, real_argv, real_path0 = sys.modules["__main__"], sys.argv, sys.path[0]
    sys.modules["__main__"] = module
    sys.argv, sys.path[0] = [path], program_dir
    sys.stdout = out
    try:
        exec(code, module.__dict__)
        outcome = ["ok"]
    except BaseException as e:  # the program's own exception, of any class
        outcome = TRACE.exc_lines(e)
    finally:
        sys.stdout = real
        sys.modules["__main__"] = real_main
        sys.argv, sys.path[0] = real_argv, real_path0
    text = out.getvalue()
    print("\n".join([f"--- stdout {len(text)}\n" + text, "--- outcome", *outcome]))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "",
         sys.argv[3] if len(sys.argv) > 3 else "")

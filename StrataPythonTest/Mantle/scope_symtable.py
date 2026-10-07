#!/usr/bin/env python3
"""Write CPython's symbol-table classification of each Python-on-Mantle test program.

For every `NAME.py` in `DIR`, by default `mantle_tests/` beside this script, writes
`NAME.symtable`: each scope's names, with the scope and the flags CPython's `symtable` module
records for them, then the `__qualname__` of every code object.
`StrataPythonTestExtra/PyScopeTest.lean` compares these files with
`PyScope.Table.symtableFormat`.

Run it with CPython 3.12 or 3.13, which give the same output:

    python3.12 StrataPythonTest/Mantle/scope_symtable.py [DIR]

3.12 is the reference: it is the first version whose symbol table inlines list, set and
dict comprehensions into the enclosing scope (PEP 709), as the scope pass does.  3.14 is
not accepted: it gives every module, class and function an `__annotate__` scope.

Annotations are replaced by `0` before the analysis.  The scope pass treats them as
unevaluated, as Python 3.14's deferred annotations are, whereas 3.12 and 3.13 evaluate
parameter and return annotations in the enclosing scope.  `ast.unparse` renumbers lines, so
an error's line comes from the original program, which must raise the same error.

A program that uses `type` statements or type parameters gets a file containing only
`skip`, and is not compared: the scope pass rejects them, and does not model the annotation
scopes CPython creates for them.  A program that this CPython cannot parse is an error, and
no file is written for it.
"""

import ast
import symtable
import sys
from pathlib import Path

SCOPES = {
    symtable.LOCAL: "local",
    symtable.GLOBAL_EXPLICIT: "global explicit",
    symtable.GLOBAL_IMPLICIT: "global implicit",
    symtable.FREE: "free",
    symtable.CELL: "cell",
}

# The `DEF_*` and `USE` bits of `Symbol._Symbol__flags`, in the order the dump prints them.
# `DEF_COMP_ITER` and `DEF_COMP_CELL` are not exported; these are their values in 3.12's and
# 3.13's `Include/internal/pycore_symtable.h`.
FLAGS = [
    (0x004, "parameter"),
    (0x002, "assigned"),
    (0x080, "imported"),
    (0x010, "referenced"),
    (0x001, "declared_global"),
    (0x008, "nonlocal"),
    (0x100, "annotated"),
    (0x200, "comp_iter"),
    (0x040, "free_class"),
    (0x800, "comp_cell"),
]

FLAG_MASK = (1 << symtable.SCOPE_OFF) - 1


class StripAnnotations(ast.NodeTransformer):
    """Replace every annotation by `0`, recording whether there was one."""

    def __init__(self):
        self.changed = False

    def visit_arg(self, node):
        if node.annotation is not None:
            node.annotation = None
            self.changed = True
        return node

    def _visit_def(self, node):
        if node.returns is not None:
            node.returns = None
            self.changed = True
        self.generic_visit(node)
        return node

    visit_FunctionDef = _visit_def
    visit_AsyncFunctionDef = _visit_def

    def visit_AnnAssign(self, node):
        node.annotation = ast.Constant(0)
        self.changed = True
        self.generic_visit(node)
        return node


def uses_type_params(tree):
    """Whether the program has a `type` statement or a type parameter list."""
    return any(isinstance(node, ast.TypeAlias) or getattr(node, "type_params", None)
               for node in ast.walk(tree))


def scope_lines(table, depth, out):
    kind = table.get_type()
    kind = kind if isinstance(kind, str) else kind.name.lower()
    out.append("  " * depth + f"{kind} {table.get_name()}")
    for sym in sorted(table.get_symbols(), key=lambda s: s.get_name()):
        raw = sym._Symbol__flags
        scope = SCOPES[(raw >> symtable.SCOPE_OFF) & symtable.SCOPE_MASK]
        flags = [name for bit, name in FLAGS if raw & FLAG_MASK & bit]
        suffix = f" ({', '.join(flags)})" if flags else ""
        out.append("  " * (depth + 1) + f"{sym.get_name()}: {scope}{suffix}")
    for child in table.get_children():
        scope_lines(child, depth + 1, out)


def qualnames(code, out):
    for const in code.co_consts:
        if hasattr(const, "co_qualname"):
            out.append(const.co_qualname)
            qualnames(const, out)


def describe(path):
    source = path.read_text()
    try:
        tree = ast.parse(source, str(path))
    except SyntaxError as err:
        version = ".".join(map(str, sys.version_info[:2]))
        sys.exit(f"{path}: not valid Python {version}: {err.msg} (line {err.lineno})")
    if uses_type_params(tree):
        return "skip\n"
    stripper = StripAnnotations()
    tree = stripper.visit(tree)
    if stripper.changed:
        source = ast.unparse(ast.fix_missing_locations(tree))
    try:
        table = symtable.symtable(source, path.name, "exec")
    except SyntaxError as err:
        if stripper.changed:
            # Take the line from the original program, if it raises the same error.
            try:
                symtable.symtable(path.read_text(), path.name, "exec")
            except SyntaxError as orig:
                if orig.msg == err.msg:
                    err = orig
                else:
                    sys.exit(f"{path}: annotations change the SyntaxError: {err}")
            else:
                sys.exit(f"{path}: replacing annotations causes a SyntaxError: {err}")
        return f"error: {err.msg} (line {err.lineno})\n"
    out = []
    scope_lines(table, 0, out)
    names = []
    qualnames(compile(source, path.name, "exec"), names)
    out.append("qualnames: " + ", ".join(sorted(names)))
    return "\n".join(out) + "\n"


def main():
    if sys.version_info[:2] not in [(3, 12), (3, 13)]:
        sys.exit("run this script with CPython 3.12 or 3.13; see the module docstring")
    if len(sys.argv) > 2:
        sys.exit(f"usage: {sys.argv[0]} [DIR]")
    test_dir = Path(sys.argv[1]) if len(sys.argv) == 2 else Path(__file__).parent / "mantle_tests"
    for path in sorted(test_dir.glob("*.py")):
        path.with_suffix(".symtable").write_text(describe(path))


if __name__ == "__main__":
    main()

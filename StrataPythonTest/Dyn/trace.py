"""CPython's side of the differential runner: run a Python file as `__main__` and print its
trace, in the text that `StrataPython.Dyn.Sem.runModuleThen` prints for the model's run.

    python3.12 trace.py FILE.py

The file runs in a fresh module named `__main__`, which has no `__file__`, and which is
`sys.modules["__main__"]` while it runs.  The trace has
three sections: `--- stdout <n>`, the n characters that the program printed, exactly;
`--- outcome`, `ok` or `raised <ExcType>: <str(exc)>` with a line `  cause <ExcType>` or
`  context <ExcType>` per link of the exception's chain; and `--- globals`, `<name> = <render>`
for each global, sorted by name, the dunder names left out but `__name__`, `__doc__` and
`__annotations__`.  `render` is the model's (`Run.lean`): `repr` for `None`, `bool`, `int`,
`float`, `str`, `bytes`, `range`, `slice`, `Ellipsis` and `NotImplemented`; containers in full, a
set's members sorted by their render; `<class 'Q'>` for a class; `<T object>` for any other
object, `T` its type's `__qualname__`; and `...` for an object inside itself.  A file that
CPython does not compile prints `--- syntax error` alone.

Run it twice, with `PYTHONHASHSEED` 0 and 1, to see whether the trace depends on the seed.

The program runs with `/` as its working directory, so that its trace doesn't depend on where the
test runs.  `render` may still run the program's code: a class's `__qualname__` goes through its
metaclass's `__getattribute__`.  The traces then differ, and the test fails.
"""

import io
import os
import sys
import types


def render(v, seen):
    if v is None or type(v) in (bool, int, float, str, bytes, range):
        return repr(v)
    if type(v) is slice:
        return f"slice({render(v.start, seen)}, {render(v.stop, seen)}, {render(v.step, seen)})"
    if v is Ellipsis:
        return "Ellipsis"
    if v is NotImplemented:
        return "NotImplemented"
    if type(v) is tuple:
        parts = [render(x, seen) for x in v]
        return f"({parts[0]},)" if len(parts) == 1 else f"({', '.join(parts)})"
    if issubclass(type(v), type):
        return f"<class '{v.__qualname__}'>"
    if id(v) in seen:
        return "..."
    inner = seen | {id(v)}
    if type(v) is list:
        return "[" + ", ".join(render(x, inner) for x in v) + "]"
    if type(v) is dict:
        return "{" + ", ".join(f"{render(k, inner)}: {render(x, inner)}" for k, x in v.items()) + "}"
    if type(v) is set:
        parts = sorted(render(x, inner) for x in v)
        return "{" + ", ".join(parts) + "}" if parts else "set()"
    if type(v) is frozenset:
        parts = sorted(render(x, inner) for x in v)
        return "frozenset({" + ", ".join(parts) + "})" if parts else "frozenset()"
    return f"<{type(v).__qualname__} object>"


def exc_lines(e):
    lines = [f"raised {type(e).__qualname__}: {e}"]
    seen = {id(e)}
    while True:
        if e.__cause__ is not None:
            e, kind = e.__cause__, "cause"
        elif e.__context__ is not None and not e.__suppress_context__:
            e, kind = e.__context__, "context"
        else:
            break
        if id(e) in seen:  # a cycle, which CPython's traceback printer also stops at
            break
        seen.add(id(e))
        lines.append(f"  {kind} {type(e).__qualname__}")
    return lines


def render_or_note(v):
    """`render(v)`, or a note if CPython can't render it (`repr` of a huge int raises)."""
    try:
        return render(v, frozenset())
    except Exception as e:  # the model stops with a gap on such a value
        return f"<no render: {type(e).__qualname__}>"


def main(path):
    if sys.version_info[:2] != (3, 12):
        sys.exit(f"trace.py needs CPython 3.12, not {sys.version.split()[0]}")
    with open(path, encoding="utf-8") as f:
        source = f.read()
    try:
        code = compile(source, path, "exec")
    except SyntaxError:
        print("--- syntax error")
        return
    os.chdir("/")
    module = types.ModuleType("__main__")
    globs = module.__dict__
    out = io.StringIO()
    real = sys.stdout
    # The module is `sys.modules["__main__"]` while it runs, as in `python FILE.py`, so that a
    # lookup through `sys.modules` (pickle, for one) finds the program's own names.
    real_main = sys.modules["__main__"]
    sys.modules["__main__"] = module
    sys.stdout = out
    try:
        exec(code, globs)
        outcome = ["ok"]
    except BaseException as e:  # the program's own exception, of any class
        outcome = exc_lines(e)
    finally:
        sys.stdout = real
        sys.modules["__main__"] = real_main
    text = out.getvalue()
    lines = [f"--- stdout {len(text)}\n" + text, "--- outcome", *outcome, "--- globals"]
    for name in sorted(globs):
        if name.startswith("__") and name.endswith("__") and \
                name not in ("__name__", "__doc__", "__annotations__"):
            continue
        lines.append(f"{name} = {render_or_note(globs[name])}")
    print("\n".join(lines))


if __name__ == "__main__":
    main(sys.argv[1])

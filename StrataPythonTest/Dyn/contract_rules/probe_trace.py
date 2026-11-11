"""CPython's side of the contract operations' probes: run a probe file as `__main__`, then
evaluate its `# python:` line, and print the trace that `trace.py` prints, followed by the
section that `StrataPython.Dyn.Sem.runModuleThen` prints for the probe's function:

    python3.12 probe_trace.py FILE.py

    --- result __main__.__probe__
    <render of the value>        (or: raised <ExcType>: <str(exc)>, with its chain's lines)

The `# python:` line is an expression.  It sees the program's globals, and the module
`contract_rules_ref`, whose functions follow the docstrings of the operations that differ from
the Python they stand for.  The module is not a global of the program, so the trace's globals are
the program's own.
"""

import importlib.util
import io
import os
import sys
import types

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import contract_rules_ref  # noqa: E402


def load_trace():
    """`StrataPythonTest/Dyn/trace.py`, by its path: the standard library has a module `trace`."""
    spec = importlib.util.spec_from_file_location("dyn_trace", os.path.join(os.path.dirname(HERE), "trace.py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


trace = load_trace()


def probe_expr(source):
    """The expression of the `# python:` line of `source`."""
    lines = [l for l in source.splitlines() if l.startswith("# python: ")]
    if len(lines) != 1:
        sys.exit("a probe needs exactly one '# python:' line")
    return lines[0][len("# python: "):]


def main(path):
    if sys.version_info[:2] != (3, 12):
        sys.exit(f"probe_trace.py needs CPython 3.12, not {sys.version.split()[0]}")
    # `python FILE` decodes the bytes by their byte order mark or coding line, and this script
    # decodes them the same way.
    with open(path, "rb") as f:
        source = importlib.util.decode_source(f.read())
    expr = probe_expr(source)
    code = compile(source, path, "exec")
    probe = compile(expr, "<probe>", "eval")
    os.chdir("/")
    module = types.ModuleType("__main__")
    globs = module.__dict__
    out = io.StringIO()
    real = sys.stdout
    real_main = sys.modules["__main__"]
    sys.modules["__main__"] = module
    sys.stdout = out
    try:
        exec(code, globs)
        outcome = ["ok"]
    except BaseException as e:  # the program's own exception, of any class
        outcome = trace.exc_lines(e)
    finally:
        sys.stdout = real
    text = out.getvalue()
    lines = [f"--- stdout {len(text)}\n" + text, "--- outcome", *outcome, "--- globals"]
    for name in sorted(globs):
        if name.startswith("__") and name.endswith("__") and \
                name not in ("__name__", "__doc__", "__annotations__"):
            continue
        lines.append(f"{name} = {trace.render_or_note(globs[name])}")
    lines.append("--- result __main__.__probe__")
    sys.stdout = io.StringIO()
    try:
        result = [trace.render_or_note(eval(probe, globs, {"contract_rules_ref": contract_rules_ref}))]
    except BaseException as e:  # the operation's exception, of any class
        result = trace.exc_lines(e)
    finally:
        sys.stdout = real
        sys.modules["__main__"] = real_main
    print("\n".join(lines + result))


if __name__ == "__main__":
    main(sys.argv[1])

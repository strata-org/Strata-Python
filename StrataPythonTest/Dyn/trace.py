"""CPython's side of the differential runner: run a Python file as `__main__` and print its
trace, in the text that `StrataPython.Dyn.Sem.runModuleThen` prints for the model's run.

    python3.12 trace.py FILE.py

The file runs in a fresh module named `__main__`, which has no `__file__`, and which is
`sys.modules["__main__"]` while it runs, with `python FILE.py`'s `sys.argv` and `sys.path[0]`.
The trace has
three sections: `--- stdout <n>`, the n characters that the program printed, exactly;
`--- outcome`, `ok` or `raised <ExcType>: <str(exc)>` with a line `  cause <ExcType>` or
`  context <ExcType>` per link of the exception's chain; and `--- globals`, `<name> = <render>`
for each global, sorted by name (a key that isn't a `str` comes last, as its `repr`), the dunder
names left out but `__name__`, `__doc__` and
`__annotations__`.  `render` is the model's (`Run.lean`): `repr` for `None`, `bool`, `int`,
`float`, `str`, `bytes`, `range`, `slice`, `Ellipsis` and `NotImplemented`; containers in full, a
set's members sorted by their render; `<class 'Q'>` for a class; `<T object>` for any other
object, `T` its type's `__qualname__`; and `...` for an object inside itself.  A file that
CPython does not compile prints `--- syntax error` alone.

Run it twice, with `PYTHONHASHSEED` 0 and 1, to see whether the trace depends on the seed.

The program runs in a fresh empty directory, whose path the trace shows as `<cwd>`, so that its
trace doesn't depend on where the test runs, and a program that writes a file can.  The path
depends only on the program's path inside the package, so that a trace that shows a part of it is
the same in every checkout.  `render` may still run the program's code: a class's `__qualname__`
goes through its metaclass's `__getattribute__`.  The traces then differ, and the test fails.  A
program that writes to file descriptor 1 without `sys.stdout` makes this script fail, since the
trace can't hold that output.
"""

import fcntl
import hashlib
import importlib.util
import io
import os
import shutil
import stat
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
    try:
        text = str(e)
    except BaseException:  # CPython's traceback printer shows the same note
        text = "<exception str() failed>"
    lines = [f"raised {type(e).__qualname__}: {text}"]
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


# The root of the programs' directories: a fixed path, not the user's temp dir, so that a part of
# a directory's path is the same in every checkout.  The tracer makes it private to the user who
# made it.  A test of the tracer itself gives a root of its own in STRATA_TRACE_ROOT, made absolute
# here, before the run changes the working directory; an empty value counts as unset, so that it
# doesn't name the current directory.
TRACE_ROOT = os.path.abspath(os.environ.get("STRATA_TRACE_ROOT") or "/tmp/strata-trace")

# The package's root: the directory that holds `StrataPythonTest/`, of which this file is
# `StrataPythonTest/Dyn/trace.py`.
PACKAGE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))


def key_text(k):
    """The `repr` of a global's key that isn't a `str`, or a note if that `repr` raises."""
    try:
        return repr(k)
    except Exception as e:
        return f"<no repr: {type(e).__qualname__}>"


def package_path(path):
    """The path of the program `path` inside the package, or its real path if it is outside."""
    real = os.path.realpath(path)
    rel = os.path.relpath(real, PACKAGE)
    return real if rel.startswith("..") else rel


def remove_tree(path):
    """Remove the directory `path` and everything in it, also the directories that the program made
    read-only or unreadable, or unlink the symlink or file that the program put at `path`; an entry
    that still can't be removed raises."""
    if not os.path.lexists(path):
        return
    if os.path.islink(path) or not os.path.isdir(path):
        os.unlink(path)
        return
    # Each directory needs its owner's permissions before its entries can be listed and removed;
    # the walk doesn't follow a symlink, so no mode outside the tree changes.  Removing a file
    # needs only its directory's permissions.
    dirs = [path]
    while dirs:
        d = dirs.pop()
        os.chmod(d, stat.S_IRWXU)
        with os.scandir(d) as entries:
            dirs.extend(e.path for e in entries if e.is_dir(follow_symlinks=False))
    shutil.rmtree(path)


def main(path):
    if sys.version_info[:2] != (3, 12):
        sys.exit(f"trace.py needs CPython 3.12, not {sys.version.split()[0]}")
    # `python FILE` decodes the bytes by their byte order mark or coding line. compile skips the
    # bytes of a comment, so decode_source checks that they decode too.
    with open(path, "rb") as f:
        source = f.read()
    try:
        importlib.util.decode_source(source)
        code = compile(source, path, "exec")
    except (SyntaxError, UnicodeDecodeError):
        print("--- syntax error")
        return
    program_dir = os.path.dirname(os.path.realpath(path))
    # The program runs in a fresh empty directory, so that a program that writes a file can.  The
    # directory's path depends only on the program's path inside the package, so that a trace that
    # shows a part of it is the same in every checkout; and each program has its own, so that the
    # runs of a suite, which run at the same time, don't share one.  A run of the same program from
    # another checkout at the same time stops at once, rather than wait and spend its time limit.
    cwd = os.path.join(TRACE_ROOT, os.path.basename(path) + "-" + hashlib.sha256(
        package_path(path).encode()).hexdigest()[:16])
    # The modes of the directories and files that the run makes, the program's included, don't
    # depend on the caller's umask.
    os.umask(0o022)
    os.makedirs(TRACE_ROOT, mode=0o700, exist_ok=True)
    root = os.lstat(TRACE_ROOT)
    if not stat.S_ISDIR(root.st_mode) or root.st_uid != os.getuid():
        sys.exit(f"trace.py: {TRACE_ROOT} is not a directory of this user")
    os.chmod(TRACE_ROOT, 0o700)
    lock = os.open(cwd + ".lock", os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        sys.exit(f"trace.py: another run of {path} is using {cwd}")
    # A run that was killed (by a timeout), or whose last cleanup failed, may have left the
    # directory behind.
    remove_tree(cwd)
    os.makedirs(cwd)
    os.chdir(cwd)
    # The paths that the trace shows as `<cwd>`, read before the program can change the directory.
    # The longer path first: one may contain the other (`/var` and `/private/var` on macOS).
    paths = sorted({os.path.realpath(cwd), cwd}, key=len, reverse=True)
    # The directory is removed when the run returns or raises, also when rendering the outcome
    # raises; a run killed by its time limit leaves it behind, and the next run removes it.
    try:
        module = types.ModuleType("__main__")
        globs = module.__dict__
        out = io.StringIO()
        real = sys.stdout
        # The module is `sys.modules["__main__"]` while it runs, as in `python FILE.py`, so that a
        # lookup through `sys.modules` (pickle, for one) finds the program's own names. The program
        # also sees `python FILE.py`'s `sys.argv` and `sys.path[0]`, so that it imports its own
        # sibling modules and not this script's.
        real_main, real_argv, real_path0 = sys.modules["__main__"], sys.argv, sys.path[0]
        # Output that bypasses `sys.stdout` (`os.write(1, ...)`, `sys.__stdout__`, a subprocess)
        # goes to a file in place of this script's stdout, since the trace can't hold it.
        real_dunder = sys.__stdout__
        real_dunder.flush()
        real_fd1 = os.dup(1)
        # A file that is unlinked at once, made without an import, unlike tempfile.
        stray_path = os.path.join(os.environ.get("TMPDIR", "/tmp"), f"trace-stray-{os.getpid()}")
        stray = os.open(stray_path, os.O_RDWR | os.O_CREAT | os.O_EXCL, 0o600)
        os.unlink(stray_path)
        os.dup2(stray, 1)
        sys.modules["__main__"] = module
        sys.argv, sys.path[0] = [path], program_dir
        sys.stdout = out
        try:
            exec(code, globs)
            outcome = ["ok"]
        except BaseException as e:  # the program's own exception, of any class
            outcome = exc_lines(e)
        finally:
            sys.stdout = real
            sys.modules["__main__"] = real_main
            sys.argv, sys.path[0] = real_argv, real_path0
            sys.__stdout__ = real_dunder
            real_dunder.flush()
            os.dup2(real_fd1, 1)
            os.close(real_fd1)
        if os.lseek(stray, 0, os.SEEK_END) > 0:
            sys.exit(f"trace.py: {path} wrote to file descriptor 1 outside sys.stdout")
        def mask(s):
            for path in paths:
                s = s.replace(path, "<cwd>")
            return s

        text = mask(out.getvalue())
        lines = [f"--- stdout {len(text)}\n" + text, "--- outcome", *outcome, "--- globals"]
        # A program may store a global under a key that isn't a `str`; such keys come last.
        for name in sorted(globs, key=lambda k: (0, k) if isinstance(k, str) else (1, key_text(k))):
            if not isinstance(name, str):
                lines.append(f"{key_text(name)} = {render_or_note(globs[name])}")
                continue
            if name.startswith("__") and name.endswith("__") and \
                    name not in ("__name__", "__doc__", "__annotations__"):
                continue
            lines.append(f"{name} = {render_or_note(globs[name])}")
        print(mask("\n".join(lines)))
    finally:
        os.chdir("/")
        # A directory that this cleanup can't remove is removed, or reported, by the next run.
        try:
            remove_tree(cwd)
        except OSError:
            pass
        os.close(lock)


if __name__ == "__main__":
    main(sys.argv[1])

"""CPython's side of the differential runner: run a Python file as `__main__` and print its
trace, in the text that `StrataPython.Dyn.Sem.runModuleThen` prints for the model's run.

    python3.12 trace.py FILE.py

The file runs in a fresh module named `__main__`, which starts with `python FILE`'s
`__annotations__ = {}`, `__cached__ = None` and `__loader__`, but has no `__file__`, and which is
`sys.modules["__main__"]` while it runs, with `python FILE.py`'s `sys.argv` and `sys.path[0]`. The
trace has three sections: `--- stdout <n>`, the n characters that the program printed, exactly;
`--- outcome`, `ok` or `raised <ExcType>: <str(exc)>` with a line `  cause <ExcType>` or
`  context <ExcType>` per link of the exception's chain; and `--- globals`, `<name> = <render>` for
each global, sorted by name (a key that isn't exactly a `str` comes last, as its render), the dunder
names left out but `__name__`, `__doc__` and `__annotations__` (unless the program has no
annotations and it is still the module's first, empty dict).  `render` is the model's
(`Run.lean`): `repr` for `None`, `bool`, `int`, `float`, `str`, `bytes`, `range`, `slice`,
`Ellipsis` and `NotImplemented`; containers in full, a set's members sorted by their render;
`<class 'Q'>` for a class; `<T object>` for any other object, `T` its type's `__qualname__`;
`<marker NAME>` for the loop-invariant marker `NAME` of the `pyhard` module, which this script
imports from `Python/pyhard/` before the program runs, found by identity among the two markers that
it held then; and `...` for an object inside itself.  A file that CPython does not compile prints
`--- syntax error` alone.

Run it twice, with `PYTHONHASHSEED` 0 and 1, to see whether the trace depends on the seed.

The program runs in a fresh empty directory, whose path the trace shows as `<cwd>`, and the
package's root shows as `<package>` (in a code object's file name, for one), so that its trace
doesn't depend on where the test runs, and a program that writes a file can.  The path depends
only on the program's path inside the package, so that a trace that shows a part of it is the same
in every checkout.  After the program, its uncaught exception is reported as `python FILE` reports
it, through the current `sys.excepthook` (`report`), and its threads, its exit handlers and the
finalizers of its module run, and what they print belongs to the program's output; up to the
module's teardown, it is in `python FILE`'s order.  The teardown itself isn't reproduced: the
module's finalizers run in the collector's order, objects held elsewhere (another module, the
builtins) are finalized later or not at all, a daemon thread, or any thread once a `threading` exit
callback has raised, keeps running where `python FILE` doesn't wait for it, and a finalizer of the
module can start a thread, where `python FILE` raises `RuntimeError`.  This script reproduces a
program that doesn't reach the interpreter's runtime, which it shares: a program that imports a
runtime module (`sys`, `io`, `os`, `gc`, `threading` and the like), names `__builtins__`, a frame or
the globals behind a function (also inside a string), or reaches a name or a namespace dynamically
(`getattr` with a computed name, `globals()`, `eval`, `open`, `attrgetter`, `help("sys")`) is cut
right at its end (`reaches_runtime`), so that the differential test gives it a gap at best.  Its
output before the cut may still differ from `python FILE`'s, since it may see this script's frames,
modules and classes; the cut keeps such a program from agreeing.  What stays outside this bound is a
program that reaches the runtime only through an object that a library hands it, through a name
that it builds at run time, or through a module of its own whose cached code doesn't match its
source.  The trace also ends with a line `--- teardown after <n>`, where only its first n
characters of output are `python FILE`'s and the differential test gives the program a gap, when:
- anything that the program made can still run code at the teardown (`runs_at_teardown`);
- the program installed a trace, profile or monitoring hook, which would also see this script's
  code, or started a process;
- this script's own `str` of the outcome's exception would run the program's code a second time;
- CPython's report of the exception, or its last flush of a `sys.stdout` or `sys.stderr` that the
  program replaced or changed, would run the program's code.
Some of these checks (a gc callback, a replaced stream or hook) can fire only for a program that
reaches the runtime; they still matter for one that reaches it through a library's object.  This
script's code reads its own copies of the builtins and of the modules that it calls, so a program
that rebinds one of them changes nothing in it.  A program fails if it adds an audit hook, which
can't be removed, forks, since a child's output doesn't reach the trace, or changes the capture of
its output.  A program that reaches this script's own frames or objects is beyond any such check.
The run also differs from `python FILE` in ways that no line marks:
- the program sees the modules that this script imported (`hashlib`, for one);
- its module has no `__file__`, which `help` of a class also reads;
- it reaches a recursion depth 2 frames lower, and the C limit 3 levels lower; a write to
  `sys.stdout` at the deepest depth raises `RecursionError`, since the capture's `write` is a
  Python frame;
- its `sys.stdout` is this script's below the text layer (`sys.stdout.fileno()` raises, and
  `sys.stdout.buffer.raw` isn't a `FileIO`);
- the collector runs at other points, since this script's allocations shift its counts, so a
  finalizer of cyclic garbage may print at another point;
- a hash or an order by identity (`hash` of a class or a function, `id(A) < id(B)`, and so the
  order of a set of them) follows this script's heap layout, which the hash seed doesn't change;
- a library that walks its caller's frames past the program's own (`enum.Enum._create_`) sees this
  script's frames;
- a string that this script's modules interned is the program's too (`is` of a `NamedTuple`'s
  field name), and `abc.get_cache_token()` counts this script's own registration;
- a signal handler of the program may run during this script's own code after the program.
TraceScriptTest pins what the first five do, and the verdict, a gap today, that a program with each
of them but the last gets.  A module of the program's own directory that it imports is checked for
the runtime as the program is, and one named like a module that this script has loaded cuts the
trace at 0, since `python FILE` would import it.  The lines up to a coding line are read undecoded,
as `python FILE` reads them, and an encoding that doesn't keep the lines' bytes (`cp037`)
fails.  The differential test runs two hash seeds, which are only a sample of the seeds that
`python FILE` may run with, so the semantics must refuse any order that depends on the
seed.  `render` reads a class's `__qualname__` from the class itself and compares types by identity,
and the globals' keys render as values do, so rendering runs none of the program's code.  If a
program writes to file descriptor 1 without `sys.stdout` or writes bytes that aren't UTF-8, this
script fails, since the trace can't hold that output; so it does if a thread of the program prints
while the globals render.  The program's `sys.stdout` is built as `python FILE` builds it on a pipe,
with no line buffering whatever the host's terminal and environment, and writes UTF-8 with
`surrogateescape`, as under a C.UTF-8 locale, whatever the host's locale.  The trace, or a failure's
message, is this script's last act: it ends with `os._exit`, so no code that the program left behind
runs after it.
"""

import ast
import atexit
import builtins
import fcntl
import gc
import hashlib
import importlib.util
import io
import _io
import os
import stat
import sys
import types
import _weakref

# This script's own builtins, and its own view of the modules that it calls: copies, taken when it
# loads, which its code reads, so that a program that rebinds a builtin, a module's function or
# `gc.callbacks` changes nothing that this script does.  `sys` stays the module, since the
# program's streams are read through it; the functions of `sys` that this script calls after the
# program are bound here.
__builtins__ = dict(builtins.__dict__)
real_io = io  # the module itself, whose `open` CPython's report of an exception calls
atexit, fcntl, gc, hashlib, io, os, stat, types, _weakref, _io = (
    types.SimpleNamespace(**vars(m))
    for m in (atexit, fcntl, gc, hashlib, io, os, stat, types, _weakref, _io))
os.path = types.SimpleNamespace(**vars(os.path))
exc_info, current_frames = sys.exc_info, sys._current_frames
modules = sys.modules  # the interpreter's own dict, whatever the program rebinds `sys.modules` to
# The `sys` module's own namespace, which CPython's C code reads and writes directly, so that this
# script's reads of `sys` after the program run no code of a class that the program gave `sys`.
sys_vars = vars(sys)
# Calls a hook of the program from a frame whose builtins are the builtins module, as CPython calls
# it with no Python frame at all, so that what the hook's C code looks up there (`__import__`) is
# what the program left there, not this script's copy.
call_hook = eval("lambda hook, *args: hook(*args)", {"__builtins__": builtins})
default_excepthook, default_unraisablehook = sys.excepthook, sys.unraisablehook
settrace, setprofile = sys.settrace, sys.setprofile
monitoring = types.SimpleNamespace(**vars(sys.monitoring))


def fail(message):
    """Ends this script with `message` on its stderr, as `sys.exit` does, which a program may have
    rebound."""
    raise SystemExit(message)


# A class's `__qualname__`, read from the class itself, so that no metaclass's code runs.
_qualname = type.__dict__["__qualname__"].__get__


def qualname(c):
    """The class `c`'s `__qualname__`, read from the class itself and made an exact `str`, so that
    no metaclass's code and no method of a `str` subclass runs."""
    return str.__str__(_qualname(c))
# An exception's links, read from the exception itself, so that no property of its class runs.
cause = BaseException.__dict__["__cause__"].__get__
context = BaseException.__dict__["__context__"].__get__
suppress_context = BaseException.__dict__["__suppress_context__"].__get__


# The types that render as their `repr`, by identity, so that no metaclass's `__eq__` runs.
PLAIN = frozenset(map(id, (bool, int, float, str, bytes, range)))

# The `pyhard` module, which the programs that state loop invariants import, loaded
# before the program runs, and its two markers, recorded then, so that the program can't change
# what counts as a marker.  Python writes no bytecode next to it.  Its directory leaves the module
# path again, so that the program sees `python FILE.py`'s path, and its imports of `pyhard` find
# the module already loaded.
sys.dont_write_bytecode = True
PYHARD_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(
    __file__)))), "Python", "pyhard")
sys.path.insert(0, PYHARD_DIR)
import pyhard  # noqa: E402
sys.path.remove(PYHARD_DIR)

if os.path.dirname(os.path.realpath(pyhard.__file__)) != os.path.realpath(PYHARD_DIR):
    sys.exit(f"trace.py: pyhard comes from {pyhard.__file__}, not from {PYHARD_DIR}")

MARKERS = ((pyhard.loop_invariant, "loop_invariant"), (pyhard.OLD, "OLD"))


def marker_name(v):
    """The name of the `pyhard` marker that `v` is, or `None`: `v` must be that very object."""
    for m, name in MARKERS:
        if v is m:
            return name
    return None


def render(v, seen):
    name = marker_name(v)
    if name is not None:
        return f"<marker {name}>"
    if v is None or id(type(v)) in PLAIN:
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
        return f"<class '{qualname(v)}'>"
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
    return f"<{qualname(type(v))} object>"


def exc_lines(e):
    # The absolute path of `pyhard`, which an `ImportError` from it names, is written relative to
    # the package, so that the trace is the same in every checkout.
    try:
        text = str(e)
    except BaseException:  # CPython's traceback printer shows the same note
        text = "<exception str() failed>"
    for d in sorted({PYHARD_DIR, os.path.realpath(PYHARD_DIR)}, key=len, reverse=True):
        text = text.replace(d, os.path.join("Python", "pyhard"))
    lines = [f"raised {qualname(type(e))}: {text}"]
    seen = {id(e)}
    while True:
        if cause(e) is not None:
            e, kind = cause(e), "cause"
        elif context(e) is not None and not suppress_context(e):
            e, kind = context(e), "context"
        else:
            break
        if id(e) in seen:  # a cycle, which CPython's traceback printer also stops at
            break
        seen.add(id(e))
        lines.append(f"  {kind} {qualname(type(e))}")
    return lines


def globals_lines(globs, first_annotations):
    """The `--- globals` lines: `<name> = <render>` for each global, sorted by name; a key that
    isn't exactly a `str` comes last, as its render.  `__annotations__` is left out while it is
    still `first_annotations`, the module's first dict, and empty; with `first_annotations` None,
    for a program that has annotations, it is always shown.  No key's own method runs: the
    items are read without a lookup, and only exact `str` keys are compared."""
    named, other = [], []
    for k, v in globs.items():
        if type(k) is not str:
            other.append((render_or_note(k), v))
        elif k == "__annotations__" and first_annotations is not None and \
                v is first_annotations and not first_annotations:
            continue
        elif not (k.startswith("__") and k.endswith("__")) or \
                k in ("__name__", "__doc__", "__annotations__"):
            named.append((k, v))
    named.sort(key=lambda kv: kv[0])
    other.sort(key=lambda kv: kv[0])
    return [f"{k} = {render_or_note(v)}" for k, v in named + other]


def render_or_note(v):
    """`render(v)`, or a note if CPython can't render it (`repr` of a huge int raises), or if the
    render holds a line break, which would split the trace's line (a class's `__qualname__` can
    hold one), as the model stops with a gap on such a render."""
    try:
        text = render(v, frozenset())
    except Exception as e:  # the model stops with a gap on such a value
        return f"<no render: {qualname(type(e))}>"
    return "<a render with a line break>" if "\n" in text else text


# The root of the programs' directories: a fixed path, not the user's temp dir, so that a part of
# a directory's path is the same in every checkout.  The tracer makes it private to the user who
# made it.  A test of the tracer itself gives a root of its own in STRATA_TRACE_ROOT, made absolute
# here, before the run changes the working directory; an empty value counts as unset, so that it
# doesn't name the current directory.
TRACE_ROOT = os.path.abspath(os.environ.get("STRATA_TRACE_ROOT") or "/tmp/strata-trace")

# The package's root: the directory that holds `StrataPythonTest/`, of which this file is
# `StrataPythonTest/Dyn/trace.py`.
PACKAGE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))


def package_path(path):
    """The path of the program `path` inside the package, or its real path if it is outside."""
    real = os.path.realpath(path)
    rel = os.path.relpath(real, PACKAGE)
    return real if rel.startswith("..") else rel


def remove_tree(path):
    """Remove the directory `path` and everything in it, also the directories that the program made
    read-only or unreadable, or unlink the symlink or file that the program put at `path`; an entry
    that still can't be removed raises.  It calls only the functions of this script's own copies of
    `os` and `stat`, so it runs no program code, also after the program rebound `os.lstat`."""
    try:
        mode = os.lstat(path).st_mode
    except FileNotFoundError:
        return
    if not stat.S_ISDIR(mode):
        os.unlink(path)
        return
    # Each directory needs its owner's permissions before its entries can be listed and removed;
    # the walk doesn't follow a symlink, so no mode outside the tree changes.  A directory is
    # removed after its entries, when it comes off the stack the second time.
    stack = [(path, False)]
    while stack:
        d, emptied = stack.pop()
        if emptied:
            os.rmdir(d)
            continue
        os.chmod(d, stat.S_IRWXU)
        stack.append((d, True))
        with os.scandir(d) as entries:
            for e in entries:
                if e.is_dir(follow_symlinks=False):
                    stack.append((e.path, False))
                else:
                    os.unlink(e.path)


def capture():
    """The raw stream under the program's standard output, the bytes that reach it, and a
    one-element list with the count of the writes that brought them.  The bytes stay readable
    after the program closes the stream, and they live in this function's variables, not on the
    stream, so that the program can't reach them through `sys.stdout.buffer.raw`, which has no
    `data`, as a `FileIO` has none."""
    data = bytearray()
    writes = [0]

    class Kept(_io._RawIOBase):  # C bases only, as a FileIO's, which no program can patch
        name, mode = "<stdout>", "wb"  # a FileIO's, which the streams' `repr` shows

        def writable(self):
            return True

        def write(self, b):
            writes[0] += 1
            data[len(data):] = b
            return len(b)

    io.RawIOBase.register(Kept)  # as a FileIO is registered, so isinstance gives the same
    return Kept(), data, writes


def flush_own(f):
    """Flush this script's own text stream `f` through its type, so that a `flush` that the program
    set on it doesn't run; an error is ignored."""
    try:
        io.TextIOWrapper.flush(f)
    except Exception:
        pass


def flush(f):
    """Flush the stream `f`, unless it is None or closed, as `python FILE` flushes `sys.stdout`
    right after the program and after its exit handlers; an error is ignored, as there (a
    detached stream, for one)."""
    try:
        if f is not None and not getattr(f, "closed", False):
            f.flush()
    except Exception:
        pass


# The audit events of the calls that install a trace, profile or monitoring hook, which would also
# see this script's own code after the program.
HOOK_EVENTS = frozenset({"sys.settrace", "sys.setprofile", "sys._settraceallthreads",
                         "sys._setprofileallthreads", "sys.monitoring.register_callback"})

# The bound of what this script reproduces: a program that reaches the interpreter's runtime, which
# this script shares with it, can change what this script does after it (its streams, its
# modules, its builtins), so its trace is cut right at its end (`reaches_runtime`).  The modules of
# the runtime, an import of which reaches it; the names and attributes that reach it, its frames
# or the objects behind a module's or a function's globals; and the builtins that reach a
# namespace or run code, which mark the program unless a call's attribute name is a literal.  A
# runtime name inside a string constant marks the program too, since a string can name an attribute
# (`attrgetter("tb_frame")`, `"{0.tb_frame}".format(e)`).
RUNTIME_MODULES = frozenset({
    "sys", "builtins", "io", "_io", "os", "posix", "nt", "gc", "atexit", "threading", "_thread",
    "weakref", "_weakref", "_weakrefset", "warnings", "_warnings", "signal", "ctypes", "_ctypes",
    "inspect", "types", "importlib", "_imp", "_frozen_importlib", "_frozen_importlib_external",
    "traceback", "linecache", "pickle", "_pickle", "copyreg", "marshal", "runpy", "code",
    "codeop", "pdb", "bdb", "faulthandler", "tracemalloc", "sysconfig", "site", "_abc", "abc",
    "subprocess", "multiprocessing", "concurrent", "asyncio", "pty", "fcntl", "resource",
    "select", "selectors", "socket", "mmap", "tempfile", "shutil", "pathlib", "_testcapi",
    # which run code that a string holds
    "timeit", "doctest"})
# The runtime modules that a library may hold as an attribute (`dataclasses.sys`).
RUNTIME_ATTRIBUTES = frozenset({
    "sys", "builtins", "io", "_io", "os", "posix", "gc", "atexit", "threading", "_thread",
    "weakref", "_weakref", "warnings", "inspect", "types", "importlib", "traceback", "linecache",
    "ctypes", "pickle", "marshal", "subprocess"})
RUNTIME_NAMES = frozenset({
    "__builtins__", "__loader__", "__spec__", "__import__", "__subclasses__", "__globals__",
    "__closure__", "__code__", "__self__", "__getattribute__", "__func__",
    "f_back", "f_globals", "f_builtins", "f_locals", "f_code", "tb_frame", "tb_next", "gi_frame",
    "cr_frame", "ag_frame", "gi_code", "cr_code", "ag_code"})
DYNAMIC_ACCESS = frozenset({"getattr", "setattr", "delattr"})
DYNAMIC_ALWAYS = frozenset({"vars", "globals", "locals", "eval", "exec", "compile", "breakpoint",
                            "__import__", "open", "attrgetter", "methodcaller", "resolve_name",
                            "locate"})
# The functions among those that a program reaches as a module's attribute (`operator.attrgetter`,
# `pkgutil.resolve_name` and `pydoc.locate`, which import the module that a string names).
DYNAMIC_ATTRIBUTES = frozenset({"attrgetter", "methodcaller", "resolve_name", "locate"})
# The names of the standard library's modules, which a library may import from the program's
# directory.
STDLIB_NAMES = sys.stdlib_module_names


def annotates(tree):
    """Whether the module `tree` has an annotation outside its functions and classes, for which
    CPython's code of the module starts with `SETUP_ANNOTATIONS`."""
    todo = [tree]
    while todo:
        node = todo.pop()
        if isinstance(node, ast.AnnAssign):
            return True
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
            todo.extend(ast.iter_child_nodes(node))
    return False


def coding_spec(line):
    """The encoding that the comment line `line` (bytes) declares, as CPython's tokenizer reads it:
    the first `coding` followed by `:` or `=`, then an ASCII name, normalized as CPython does
    (`utf-8-unix` is `utf-8`, `latin-1` is `iso-8859-1`); None if it declares none."""
    if not line.lstrip(b" \t\f").startswith(b"#"):
        return None
    k = line.find(b"coding")
    while k >= 0:
        rest = line[k + 6:]
        if rest[:1] in (b":", b"="):
            name = bytearray()
            for c in rest[1:].lstrip(b" \t"):
                if not (chr(c).isascii() and (chr(c).isalnum() or chr(c) in "-_.")):
                    break
                name.append(c)
            if name:
                n = name.decode("ascii")
                low = n[:12].lower().replace("_", "-")
                if low == "utf-8" or low.startswith("utf-8-"):
                    return "utf-8"
                if any(low == e or low.startswith(e + "-")
                       for e in ("latin-1", "iso-8859-1", "iso-latin-1")):
                    return "iso-8859-1"
                return n
        k = line.find(b"coding", k + 6)
    return None


def as_python_reads(source):
    """The program's text as `python FILE` reads the bytes `source` when they declare their encoding
    on line 1 or 2 (`coding_spec`): the lines up to that declaration are only read for it, not
    decoded, so they count as empty comments, and the rest is decoded with that encoding.  None
    without such a line, or with a byte order mark, where `compile` of the bytes reads them as
    `python FILE` does.  An unknown encoding, or a first line that isn't UTF-8 before a declaration
    on line 2, raises `SyntaxError`, and a decoding error `UnicodeDecodeError`, as each fails
    `python FILE`."""
    lines = source.splitlines(keepends=True)
    if lines:
        lines[0] = lines[0].removeprefix(b"\xef\xbb\xbf")
    if source.startswith(b"\xef\xbb\xbf"):
        # Line 2 counts only after a blank line or a comment, as below.
        first = lines[0] if lines else b""
        declared = [coding_spec(first)]
        if len(lines) > 1 and (not first.strip(b" \t\f\r\n") or
                               first.lstrip(b" \t\f").startswith(b"#")):
            declared.append(coding_spec(lines[1]))
        if any(d not in (None, "utf-8") for d in declared):
            raise SyntaxError("encoding problem with BOM")  # as `python FILE` reports it
        return None
    encoding, head = None, 0
    if lines:
        encoding, head = coding_spec(lines[0]), 1
        if encoding is None and len(lines) > 1 and (
                not lines[0].strip(b" \t\f\r\n") or lines[0].lstrip(b" \t\f").startswith(b"#")):
            encoding, head = coding_spec(lines[1]), 2
            if encoding is not None:
                lines[0].decode("utf-8")  # as `python FILE` decodes the first line
    if encoding is None:
        return None
    if b"\x00" in b"".join(lines[:head]):
        raise SyntaxError("source code cannot contain null bytes")
    if encoding == "locale":  # which a text stream reads as the locale's encoding
        encoding = real_io.TextIOWrapper(real_io.BytesIO(), encoding="locale").encoding
    try:
        ascii_lines = b"#\n".decode(encoding) == "#\n"
    except LookupError:
        raise SyntaxError(f"unknown encoding: {encoding}")  # as `python FILE` reports it
    except UnicodeError:
        ascii_lines = False
    if encoding.replace("_", "-").lower() in ("utf-16", "utf16", "utf-32", "utf32"):
        raise SyntaxError(f"encoding problem: {encoding}")  # as `python FILE` reports it
    if not ascii_lines:
        # `python FILE` splits such a file's lines as bytes, which this script doesn't reproduce
        # (`cp037`).
        fail(f"trace.py: {encoding}, the encoding of the program, doesn't keep its line breaks")
    # Decoded in pieces, as `python FILE` reads it through a text stream: a decoder can reject in
    # pieces what it takes whole (`idna` on a part over 1024 characters).
    # As `python FILE` reads it: from the coding line's last byte, its first line dropped, so that
    # the decoder sees that byte too.
    start = sum(map(len, lines[:head])) - 1
    stream = real_io.TextIOWrapper(real_io.BytesIO(source[start:]), encoding, newline=None)
    stream.readline()
    return "#\n" * head + stream.read()


def unchecked_cache(source):
    """Whether the cache of the module file `source` (its `__pycache__` file for this interpreter)
    is a hash-based one that the import uses without checking it against the source."""
    tag = sys.implementation.cache_tag
    head, tail = os.path.split(source)
    name = tail[:-3] if tail.endswith(".py") else tail
    cached = os.path.join(head, "__pycache__", f"{name}.{tag}.pyc")
    try:
        with open(cached, "rb") as f:
            flags = int.from_bytes(f.read(8)[4:8], "little")
    except OSError:
        return False
    return flags & 1 == 1 and flags & 2 == 0


def sibling_trees(tree, directory, opaque, here=None, seen=None):
    """The trees of the modules in `directory` that the program `tree` imports, and of those that
    they import in turn (a package's relative imports from `here`, its own directory, included, and
    every module of a package that is imported with `*`), so that a program that reaches the
    runtime through a module of its own is marked too.  A module that doesn't parse is left out:
    its import fails.  A module whose code this can't read (only a `.pyc` or an extension, or a
    cache that the import doesn't check) goes into `opaque`."""
    seen = set() if seen is None else seen
    trees = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            base, names = directory, [a.name for a in node.names]
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            base = directory
            names = [node.module] + [node.module + "." + a.name for a in node.names]
        elif isinstance(node, ast.ImportFrom) and node.level > 0 and here is not None:
            base = here
            for _ in range(node.level - 1):
                base = os.path.dirname(base)
            prefix = node.module + "." if node.module else ""
            names = ([node.module] if node.module else []) + [prefix + a.name for a in node.names]
        else:
            continue
        files = []
        for name in names:
            parts = name.split(".")
            for k in range(1, len(parts) + 1):
                if parts[k - 1] == "*":
                    package = os.path.join(base, *parts[:k - 1])
                    if os.path.isdir(package):
                        files += [os.path.join(top, e) for top, _, es in sorted(os.walk(package))
                                  for e in sorted(es) if e.endswith(".py")]
                    break
                stem = os.path.join(base, *parts[:k])
                # An extension module comes before a source file, and a `.pyc` or an extension
                # `__init__` makes a package without source.
                extensions = importlib._bootstrap_external.EXTENSION_SUFFIXES
                init = os.path.join(stem, "__init__")
                if any(os.path.isfile(stem + x) for x in extensions) or (
                        not os.path.isfile(stem + ".py") and os.path.isfile(stem + ".pyc")) or (
                        not os.path.isfile(init + ".py") and
                        any(os.path.isfile(init + x) for x in [".pyc"] + extensions)):
                    opaque.append(stem)
                files += [stem + ".py", os.path.join(stem, "__init__.py")]
        for f in files:
            if f in seen or not os.path.isfile(f):
                continue
            seen.add(f)
            if unchecked_cache(f):
                opaque.append(f)
            try:
                with open(f, "rb") as fh:
                    t = ast.parse(fh.read(), f)
            except (SyntaxError, ValueError, OSError):
                continue
            trees.append(t)
            trees.extend(sibling_trees(t, directory, opaque, os.path.dirname(f), seen))
    return trees


def identifiers(text):
    """The words of `text` that could be identifiers: its maximal runs of letters, digits and
    underscores."""
    words, word = [], []
    for c in text:
        if c.isalnum() or c == "_":
            word.append(c)
        elif word:
            words.append("".join(word))
            word = []
    if word:
        words.append("".join(word))
    return words


def format_fields(text):
    """The text of each replacement field `{...}` of `text` that reaches into its value (holds a
    `.` or a `[`), as `str.format` reads one."""
    fields, depth, start = [], 0, 0
    for i, c in enumerate(text):
        if c == "{":
            depth, start = depth + 1, i + 1
        elif c == "}" and depth:
            depth -= 1
            field = text[start:i]
            if "." in field or "[" in field:
                fields.append(field)
    return fields


def dotted_names(text):
    """The parts of each dotted or colon-separated name in `text` (`["sys", "stdout"]` of
    `sys.stdout`, `["0", "sys", "modules"]` of `{0.sys.modules[k]}`), but not a word at the end of a
    sentence (`types.`)."""
    names, run = [], []
    for c in text + " ":
        if c.isalnum() or c in "_.:":
            run.append(c)
            continue
        parts = "".join(run).replace(":", ".").split(".")
        if len(parts) > 1 and all(parts[1:]):  # `.sys.modules`, a format field's, counts too
            names.append(parts)
        run = []
    return names


def reaches_runtime(tree):
    """Whether the program `tree` reaches the interpreter's runtime: it imports a module of it,
    names a runtime name as a name or an attribute (or a runtime module as an attribute, such as
    `dataclasses.sys`), in a string constant or as a keyword of a class pattern, passes a
    `stacklevel`, takes the `__dict__` of a module that it imported, uses a builtin that reaches a
    namespace or runs code, or calls `getattr`, `setattr` or `delattr` with an attribute
    name that isn't a literal string outside those names.  What stays unmarked is a program that
    reaches the runtime only through objects that it is handed (a library function that returns
    one, or a module that it passes around under another name)."""
    allowed = set()  # the `getattr` names in a call with a literal attribute name
    imported = {a.asname or a.name.partition(".")[0] for node in ast.walk(tree)
                if isinstance(node, (ast.Import, ast.ImportFrom)) for a in node.names}
    for node in ast.walk(tree):
        # `getattr(o, "x")`, and `object.__getattribute__(o, "x")`, with a literal name that isn't
        # a runtime one, reach only that attribute.
        if isinstance(node, ast.Call) and (
                isinstance(node.func, ast.Name) and node.func.id in DYNAMIC_ACCESS or
                isinstance(node.func, ast.Attribute) and node.func.attr == "__getattribute__"):
            name = node.args[1] if len(node.args) > 1 else None
            if (isinstance(name, ast.Constant) and type(name.value) is str and
                    name.value not in RUNTIME_NAMES and name.value not in RUNTIME_MODULES and
                    not node.keywords and not any(isinstance(a, ast.Starred) for a in node.args)):
                allowed.add(id(node.func))
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            if any(a.name.split(".")[0] in RUNTIME_MODULES for a in node.names):
                return True
        elif isinstance(node, ast.ImportFrom):
            if node.level == 0 and (node.module or "").split(".")[0] in RUNTIME_MODULES:
                return True
            # `from operator import attrgetter as ag` names the function only as `ag`.
            if any(a.name in DYNAMIC_ATTRIBUTES for a in node.names):
                return True
        elif isinstance(node, ast.Name):
            if node.id in RUNTIME_NAMES or node.id in DYNAMIC_ALWAYS or \
                    node.id in DYNAMIC_ACCESS and id(node) not in allowed:
                return True
        elif isinstance(node, ast.Constant) and type(node.value) is str:
            # `__getattribute__` reaches only the name that it is given, which a string or a
            # computed name marks.
            if any(t in RUNTIME_NAMES and t != "__getattribute__" for t in identifiers(node.value)):
                return True
            # A dotted name of a runtime module (`"sys.stdout"`, `"sys:_getframe"`), which `help`
            # or `pkgutil.resolve_name` imports, or one through a runtime module that a library
            # holds (`"{0.sys.modules}".format(dataclasses)`).
            if any(n[0] in RUNTIME_MODULES or any(p in RUNTIME_ATTRIBUTES for p in n[1:])
                   for n in dotted_names(node.value)):
                return True
            # A format field (`"{0.__dict__[sys]}"`) reaches whatever names it holds.
            if any(t in RUNTIME_ATTRIBUTES or t in RUNTIME_MODULES or t == "__dict__"
                   for f in format_fields(node.value) for t in identifiers(f)):
                return True
        elif isinstance(node, ast.MatchClass):
            if any(k in RUNTIME_NAMES for k in node.kwd_attrs):
                return True
        elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and \
                node.func.id == "help" and any(isinstance(a, ast.Constant) and type(a.value) is str
                                               for a in node.args):
            return True  # `help("sys")` imports the module that it names
        elif isinstance(node, ast.keyword):
            # A library that walks its caller's frames (`logging`'s `stacklevel`) reaches this
            # script's own.
            if node.arg == "stacklevel":
                return True
        elif isinstance(node, ast.Attribute):
            if node.attr in RUNTIME_ATTRIBUTES or node.attr in DYNAMIC_ATTRIBUTES or \
                    node.attr in RUNTIME_NAMES and id(node) not in allowed:
                return True
            if node.attr == "__dict__" and isinstance(node.value, ast.Name) and \
                    node.value.id in imported:
                return True
    return False


# The audit events of the calls that start another process, whose output, or that of a function
# run in it before it starts its program, can come at a time that this script doesn't reproduce.
SPAWN_EVENTS = frozenset({"os.posix_spawn", "os.spawn", "os.system", "os.exec", "subprocess.Popen",
                          "os.startfile"})

# A type's MRO and a class's own namespace, read from the type itself, so that no metaclass's code
# runs; and a weak reference's callback.
mro = type.__dict__["__mro__"].__get__
namespace = type.__dict__["__dict__"].__get__
callback = _weakref.ReferenceType.__dict__["__callback__"].__get__

# Each kind of generator, with its suspended state.  `runs_at_teardown` compares types by identity,
# as a dict lookup would run a metaclass's `__hash__`.
GENERATORS = ((types.GeneratorType, "gi_suspended"), (types.CoroutineType, "cr_suspended"),
              (types.AsyncGeneratorType, "ag_suspended"))


# The callbacks with which the standard library's weak collections drop a dead entry, which no
# program can see.
STDLIB = os.path.dirname(os.__file__) + os.sep
HOUSEKEEPING = frozenset({"WeakSet.__init__.<locals>._remove",
                          "WeakValueDictionary.__init__.<locals>.remove",
                          "WeakKeyDictionary.__init__.<locals>.remove"})


def quiet_callback(c):
    """Whether the weak reference callback `c` does nothing that a program can see: one of the
    standard library's housekeeping callbacks, or the `_destroy` with which `abc` drops a dead
    class from its caches.  It reads only built-in attributes, so it runs none of the program's
    code."""
    if type(c) is types.BuiltinMethodType:
        return c.__name__ == "_destroy" and type(c.__self__) is _weakref.ReferenceType
    if type(c) is types.FunctionType:
        code = c.__code__
        return code.co_qualname in HOUSEKEEPING and code.co_filename.startswith(STDLIB)
    return False


def quiet_stream(o):
    """Whether the finalizer of `o` does nothing that a program can see: `o` is an in-memory stream
    of the io module, or a closed file of the io module's own types, layer by layer down to its
    file.  It reads only the io module's own attributes, so it runs none of the program's code."""
    try:
        while True:
            t = type(o)
            if t is io.StringIO or t is io.BytesIO:
                return True
            if t is io.FileIO:
                return o.closed
            if t is io.TextIOWrapper:
                o = o.buffer
            elif t is io.BufferedReader or t is io.BufferedWriter or t is io.BufferedRandom:
                o = o.raw
            else:
                return False
    except ValueError:  # a detached stream
        return False


def defines_del(t):
    """Whether the class `t` or one of its bases defines `__del__`, or `__release_buffer__`, which
    runs when a buffer of its object goes; it runs no program code."""
    return any("__del__" in namespace(k) or "__release_buffer__" in namespace(k) for k in mro(t))


def exit_runs_code(e):
    """Whether reading the `code` of the SystemExit `e`, as CPython's exit does, can run program
    code: a class of it that isn't builtin defines `code` or an attribute hook, or its metaclass
    isn't builtin.  It runs none of the program's code."""
    t = type(e)
    return id(type(t)) not in BUILTIN_CLASSES or any(
        id(k) not in BUILTIN_CLASSES and any(n in namespace(k) for n in
                                             ("code", "__getattr__", "__getattribute__"))
        for k in mro(t))


def is_exit(e):
    """Whether `e` is a SystemExit, by its real type, as CPython tells it, not by its `__class__`,
    which a program can set."""
    return any(k is SystemExit for k in mro(type(e)))


def runs_at_teardown(baseline, before, frozen):
    """Whether anything that the program made can still run code when the program's module and the
    interpreter are torn down, in an order or at a time that this script doesn't reproduce: an
    object whose class defines `__del__` (the io module's streams included), a suspended generator
    or coroutine, whose close can run its code, a weak reference with a callback (`weakref.finalize`
    included), a thread other than the main one, or a gc callback.  The objects of `baseline`,
    alive before the program ran, are this script's own, unless the program changed their class or
    whether it defines `__del__`; `before` maps the id of each of their classes to the class and
    to whether it defined `__del__` then.  `frozen` is the count of objects that `gc.freeze` hid
    before the program, which `gc.get_objects` doesn't list.  It runs none of the program's code."""
    if len(current_frames()) > 1 or gc.callbacks or gc.get_freeze_count() != frozen:
        return True
    known = {id(o) for o in baseline}
    same = {}  # the id of a class of `baseline` -> whether it is as it was before the program
    finalizes = {}  # the id of a class -> whether it defines `__del__`
    for o in gc.get_objects():
        t = type(o)
        if id(o) in known:
            if id(t) not in same:
                was = before.get(id(t))
                same[id(t)] = was is not None and was[0] is t and was[1] == defines_del(t)
            if same[id(t)]:
                continue
        generator = next((g for g in GENERATORS if g[0] is t), None)
        if generator is not None:
            if getattr(o, generator[1]):
                return True
            # A coroutine that never ran warns when it goes, through the program's `warnings`.
            if t is types.CoroutineType and not o.cr_suspended and not o.cr_running and \
                    o.cr_frame is not None:
                return True
        elif t is _weakref.ProxyType or t is _weakref.CallableProxyType:
            return True  # a weak proxy, whose callback can't be read
        elif issubclass(t, _weakref.ReferenceType):
            if callback(o) is not None and not quiet_callback(callback(o)):
                return True
        elif quiet_stream(o):
            continue
        else:
            if id(t) not in finalizes:
                finalizes[id(t)] = defines_del(t)
            if finalizes[id(t)]:
                return True
    return False


# The ids of the builtin classes, whose report of an exception runs no program code.
BUILTIN_CLASSES = frozenset(id(v) for v in vars(builtins).values() if type(v) is type)
# An exception's arguments and a SystemExit's code, read from their slots.
exc_args = BaseException.__dict__["args"].__get__
exit_code = SystemExit.__dict__["code"].__get__
# The slots of `BaseException` itself, which the report reads as the chain's links or as `args`.
LINK_SLOTS = ("args", "__traceback__", "__context__", "__cause__", "__suppress_context__",
              "__dict__", "__class__")
def slots_run_code(e):
    """Whether a slot of the builtin classes of the exception `e` that their `__str__` reads (an
    `OSError`'s `strerror`, for one) holds a value whose `str` can run program code; it runs none
    itself."""
    for k in mro(type(e)):
        if id(k) not in BUILTIN_CLASSES:
            continue
        for name, d in namespace(k).items():
            if name in LINK_SLOTS or not (type(d) is types.MemberDescriptorType or
                                          type(d) is types.GetSetDescriptorType):
                continue
            try:
                v = d.__get__(e)
            except Exception:  # a slot that isn't set
                continue
            if name != "obj" and not plain(v):
                return True
    return False


def plain(v, seen=frozenset()):
    """Whether `str` and `repr` of `v` run no program code: `v` is None, a value of a plain builtin
    type, or a builtin container of such values.  It runs none of the program's code."""
    if v is None or id(type(v)) in PLAIN:
        return True
    if id(v) in seen:
        return True
    t = type(v)
    if t is tuple or t is list or t is set or t is frozenset:
        return all(plain(x, seen | {id(v)}) for x in v)
    if t is dict:
        return all(plain(k, seen | {id(v)}) and plain(x, seen | {id(v)}) for k, x in v.items())
    return False


def str_runs_code(e):
    """Whether `str(e)` of the exception `e`, which the outcome's line holds, can run program code:
    a class of `e` that isn't builtin defines `__str__`, its metaclass isn't builtin, or an argument
    or a slot that its `__str__` reads isn't plain.  It runs none of the program's code."""
    t = type(e)
    if id(type(t)) not in BUILTIN_CLASSES:
        return True
    if any(id(k) not in BUILTIN_CLASSES and "__str__" in namespace(k) for k in mro(t)):
        return True
    return not plain(exc_args(e)) or slots_run_code(e)


exc_traceback = BaseException.__dict__["__traceback__"].__get__


def unraisable_args_type():
    """The type of the argument of `sys.unraisablehook`, which `sys` doesn't name: the type of what
    a temporary hook receives for a finalizer that raises."""
    received = []

    class Raises:
        def __del__(self):
            raise ValueError

    hook, sys.unraisablehook = sys.unraisablehook, received.append
    try:
        Raises()
    finally:
        sys.unraisablehook = hook
    return type(received[0])


UnraisableHookArgs = unraisable_args_type()
set_traceback = BaseException.__dict__["__traceback__"].__set__


def report(e):
    """Reports the program's uncaught exception `e` as `python FILE` does when the program ends
    with it, so that what the report runs of the program's code (an exception's `__str__`, the
    lookups of a "Did you mean" suggestion, a `sys.excepthook` of its own) runs as there: a
    SystemExit through its `code`, which is printed to `sys.stderr` unless it is None or an int;
    any other exception through the current `sys.excepthook`, with `sys.last_exc` and the other
    `sys.last_*` set, and with this script's own frame cut off the traceback."""
    if is_exit(e):
        # First, as CPython reads it before `sys.stderr`; if the lookup fails, CPython prints the
        # exception itself.
        try:
            code = getattr(e, "code", None)
        except Exception:
            code = e
        err = sys_vars.get("stderr")
        if code is None or issubclass(type(code), int):
            return
        try:
            if err is not None:
                err.write(str(code))
                err.write("\n")
        except Exception:
            pass
        return
    err = sys_vars.get("stderr")
    tb = exc_traceback(e)
    if tb is not None:
        tb = tb.tb_next  # this script's own frame, which `python FILE` doesn't have
        set_traceback(e, tb)
    sys_vars["last_exc"] = sys_vars["last_value"] = e
    sys_vars["last_type"], sys_vars["last_traceback"] = type(e), tb
    hook = sys_vars.get("excepthook")
    try:
        if hook is None:
            if err is not None:
                err.write("sys.excepthook is missing\n")
            call_hook(default_excepthook, type(e), e, tb)
        else:
            call_hook(hook, type(e), e, tb)
    except BaseException as h:
        try:
            if err is not None:
                err.write("Error in sys.excepthook:\n")
                call_hook(default_excepthook, type(h), h, exc_traceback(h))
                err.write("\nOriginal exception was:\n")
            call_hook(default_excepthook, type(e), e, tb)
        except Exception:
            pass


def main(path):
    if sys.version_info[:2] != (3, 12):
        fail(f"trace.py needs CPython 3.12, not {sys.version.split()[0]}")
    # `python FILE` decodes the bytes by their byte order mark or coding line, all of them, comments
    # included.
    with open(path, "rb") as f:
        source = f.read()
    # As `python FILE` names the file to its code and loader: joined to the working directory, with
    # its `.` and `..` kept.
    abs_path = path if os.path.isabs(path) else os.path.join(os.getcwd(), path)
    program_dir = os.path.dirname(os.path.realpath(path))
    try:
        # The text, as `python FILE` decodes it, so that `compile` reads no coding line again
        # (where it would split lines only at `\n`).
        text = as_python_reads(source)
        if text is None:
            text = source.removeprefix(b"\xef\xbb\xbf").decode("utf-8")
        code = compile(text, abs_path, "exec")
        tree = ast.parse(text, abs_path)
        opaque = []  # the modules of the program's own whose code this script can't read
        bounded = not reaches_runtime(tree) and not any(
            reaches_runtime(t) for t in sibling_trees(tree, program_dir, opaque))
        annotated = annotates(tree)
        # `python FILE` reads the file with its file tokenizer, which fails on some f-string
        # fields that span lines (`f"""{x=!r` and `}"""` on the next line) where `compile` of the
        # bytes doesn't: the whole output may differ.
        split_field = any(isinstance(n, ast.FormattedValue) and n.lineno != n.end_lineno
                          for n in ast.walk(tree))
        del tree
        # A module in the program's directory (the program's own file included, or one without
        # source) named like a module that this script has loaded is never imported here, where
        # `python FILE` imports it; and one named like a standard module may be imported by a
        # library, which the semantics' model of that library doesn't do: the whole output may
        # differ.
        shadows = any(e.partition(".")[0] in modules or e.partition(".")[0] in STDLIB_NAMES
                      for e in os.listdir(program_dir))
    except (SyntaxError, UnicodeError):
        os.write(1, b"--- syntax error\n")
        return
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
        fail(f"trace.py: {TRACE_ROOT} is not a directory of this user")
    os.chmod(TRACE_ROOT, 0o700)
    lock = os.open(cwd + ".lock", os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        fail(f"trace.py: another run of {path} is using {cwd}")
    # A run that was killed (by a timeout), or whose last cleanup failed, may have left the
    # directory behind.
    remove_tree(cwd)
    os.makedirs(cwd)
    os.chdir(cwd)
    # The paths that the trace shows as `<cwd>`, read before the program can change the directory,
    # and as `<package>`, the package's root, which a program's code names in its file name.  The
    # longer path first: one may contain the other (`/var` and `/private/var` on macOS).
    tokens = {os.path.realpath(cwd): "<cwd>", cwd: "<cwd>", PACKAGE: "<package>",
              os.path.abspath(os.path.dirname(os.path.dirname(os.path.dirname(__file__)))):
              "<package>"}
    paths = sorted(tokens, key=len, reverse=True)
    # The directory is removed when the run returns or raises, also when rendering the outcome
    # raises; a run killed by its time limit leaves it behind, and the next run removes it.
    try:
        module = types.ModuleType("__main__")
        globs = module.__dict__
        # As `python FILE` starts its `__main__`, in its order.  The program's builtins are the
        # builtins module, not the copy that this script's own functions read, which `exec` would
        # give it.
        first_annotations = globs["__annotations__"] = {}
        globs["__builtins__"] = builtins
        globs["__cached__"] = None
        globs["__loader__"] = importlib._bootstrap_external.SourceFileLoader("__main__", abs_path)
        real, real_err = sys.stdout, sys.stderr
        # The program's `sys.stdout` is built as `python FILE` builds it when its standard output is a
        # pipe: a text stream that holds its text until a flush, over a buffered byte stream of the
        # pipe's block size, so that text and bytes written to `sys.stdout.buffer` come out in
        # CPython's order.  It writes UTF-8 with `surrogateescape`, as `python FILE` does under a C
        # or C.UTF-8 locale, so that the trace doesn't depend on the host's locale.
        buf, data, writes = capture()
        size = os.fstat(1).st_blksize
        out = io.TextIOWrapper(io.BufferedWriter(buf, size if size > 1 else io.DEFAULT_BUFFER_SIZE),
                               encoding="utf-8", errors="surrogateescape")
        out.mode = "w"  # as `python FILE` sets it on its `sys.stdout`
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
        # A file in memory that can't shrink, so that a program that writes to it and truncates it
        # still leaves its bytes; where there is none (no `os.memfd_create`), a file that is
        # unlinked at once, made without an import, unlike tempfile.
        shrinks = False
        try:
            stray = os.memfd_create("trace-stray", os.MFD_ALLOW_SEALING)
            fcntl.fcntl(stray, fcntl.F_ADD_SEALS, fcntl.F_SEAL_SHRINK)
        except (AttributeError, OSError):
            shrinks = True
            stray_path = os.path.join(os.environ.get("TMPDIR", "/tmp"),
                                      f"trace-stray-{os.getpid()}")
            stray = os.open(stray_path, os.O_RDWR | os.O_CREAT | os.O_EXCL, 0o600)
            os.unlink(stray_path)
        os.dup2(stray, 1)
        # A write or a truncation changes the file's change time, so a file that can shrink still
        # shows a write that the program truncated again.  The change time comes from a clock that
        # moves once per kernel tick, so this waits for that clock to pass it: a later write then
        # gets a later change time.
        stray_changed = os.fstat(stray).st_ctime_ns
        if shrinks:
            import time  # a builtin module, which `python FILE` has loaded too
            coarse = 5 if sys.platform.startswith("linux") else time.CLOCK_REALTIME  # ..._COARSE
            while time.clock_gettime_ns(coarse) <= stray_changed:
                time.sleep(0.0005)
        sys.modules["__main__"] = module
        sys.argv, sys.path[0] = [path], program_dir
        sys.stdout = out
        try:
            # The program's exception, and so the locals of its frames, lives until after the exit
            # handlers, as in `python FILE`, where a SystemExit is dropped at once: the order of
            # the locals' finalizers and of the exit handlers depends on it.
            kept = None
            # The program's calls that install a hook, seen through an audit hook of this script's
            # own, which no program can remove or list.
            audited = set()

            spawned = []  # where the output was when the program started a process

            def audit(event, args):
                if event in HOOK_EVENTS or event in ("sys.addaudithook", "os.fork", "os.forkpty"):
                    audited.add(event)
                elif event in SPAWN_EVENTS and not spawned:
                    spawned.append(len(data))


            sys.addaudithook(audit)
            # The objects alive before the program: this script's own, which `runs_at_teardown`
            # leaves out, and their classes.
            # A program outside the bound is cut at its end anyway, so it needs no snapshot.
            frozen, baseline, before = gc.get_freeze_count(), [], {}
            if bounded:
                baseline = gc.get_objects()
                for o in baseline:
                    if id(type(o)) not in before:
                        before[id(type(o))] = (type(o), defines_del(type(o)))
                del o
            # What CPython's report of an exception and its final flushes call besides the
            # exception: the instance attributes of the standard streams, which can shadow their
            # methods, and the `io` module's functions.
            # The program's own `sys.stdout` and its buffer are held weakly, so that they go when
            # the program drops them, as under `python FILE`.
            stream_attrs = [((lambda f=f: f), dict(vars(f))) for f in
                            (real, real.buffer, real_err, getattr(real_err, "buffer", None))
                            if f is not None]
            stream_attrs += [(_weakref.ref(f), dict(vars(f))) for f in (out, out.buffer)]
            io_attrs = {k: v for k, v in vars(real_io).items() if callable(v)}

            def changed(entries):
                for ref, was in entries:
                    f = ref()
                    if f is None:
                        continue
                    now = vars(f)
                    if set(now) != set(was) or any(now[k] is not v for k, v in was.items()):
                        return True
                return False

            def report_reaches_program():
                if changed(stream_attrs):
                    return True
                now = vars(real_io)
                return any(now.get(k) is not v for k, v in io_attrs.items())

            def cut_here():
                # Where the output may start to differ: the text that this script's own stream
                # still holds is the program's, unless the program changed that stream's methods,
                # whose flush `python FILE` would then not do.
                if sys_vars.get("stdout") is out and not changed(stream_attrs[-2:]):
                    flush_own(out)
                cuts.append(len(data))

            # The capture of the program's output is this script's own object, which a program
            # can still reach through `sys.stdout`: a change to it fails the run, through functions
            # bound now.
            kept_class = type(buf)
            watched = [(namespace(kept_class), dict(namespace(kept_class)))]
            write, exit_now = os.write, os._exit

            def check_unchanged(when):
                missing = object()
                for d, was in watched:
                    if set(d) != set(was):
                        write(2, (f"trace.py: {path} changed the capture of its output "
                                  f"{when}\n").encode())
                        exit_now(1)
                    for k, v in was.items():
                        if d.get(k, missing) is not v:
                            write(2, (f"trace.py: {path} changed the capture of its output "
                                      f"{when}\n").encode())
                            exit_now(1)
                if type(buf) is not kept_class:
                    write(2, f"trace.py: {path} changed the capture of its output\n".encode())
                    exit_now(1)
            try:
                exec(code, globs)
            except BaseException as e:  # the program's own exception, of any class
                kept = e
            # The points in the output after which it may differ from `python FILE`'s: a process
            # that the program started, a hook that it installed, which would see this script's code
            # from here on, a `sys.stdout` that it left in place of this script's, whose flush is
            # its own code, and this script's own `str` of the outcome's exception, when that runs
            # the program's code a second time.
            cuts = list(spawned)
            if audited & HOOK_EVENTS:
                settrace(None)
                setprofile(None)
                for tool in range(6):
                    if monitoring.get_tool(tool) is not None:
                        monitoring.set_events(tool, 0)
                cut_here()
            # A program that reaches the runtime is outside the bound of what this script
            # reproduces: only its output up to here is compared.
            if not bounded:
                cut_here()
            if split_field or shadows or opaque:
                cuts.append(0)
            if sys_vars.get("stdout") is not out:
                cuts.append(len(data))
            check_unchanged("after the program")
            # As `python FILE` does as soon as the program ends, before it reports the exception:
            # it flushes `sys.stderr`, then `sys.stdout`, whatever objects they are, and ignores
            # an error.
            for name in ("stderr", "stdout"):
                try:
                    sys_vars[name].flush()
                except Exception:
                    pass
            # The report's text reaches the trace, or runs code that the program patched, when the
            # program replaced `sys.stderr` or `sys.excepthook`, or changed a standard stream's
            # attributes or the `io` module, and then its tracebacks name the program's file as
            # this script runs it, not as `python FILE` does: the output from here on may differ.
            if kept is not None and (
                    sys_vars.get("stderr") is not real_err or report_reaches_program() or
                    not is_exit(kept) and
                    sys_vars.get("excepthook") is not default_excepthook or
                    is_exit(kept) and (not plain(exit_code(kept)) or str_runs_code(kept) or
                                       exit_runs_code(kept))):
                cut_here()
            if kept is not None:
                report(kept)  # as `python FILE` does as soon as the program ends with it
                if str_runs_code(kept):
                    cut_here()
            outcome = ["ok"] if kept is None else exc_lines(kept)
            if kept is None or not is_exit(kept):
                # As `python FILE` does after the program, unless it ended with a SystemExit.
                globs.pop("__file__", None)
                globs.pop("__cached__", None)
            if kept is not None and is_exit(kept):
                kept = None
            threading = modules.get("threading")
            if threading is not None:
                try:
                    threading._shutdown()
                except BaseException as e:
                    # As CPython reports it: through the current `sys.unraisablehook`, for the
                    # `threading` module, with this script's own frame cut off the traceback.
                    tb = exc_traceback(e)
                    if tb is not None:
                        tb = tb.tb_next
                    hook = sys_vars.get("unraisablehook")
                    # As before the report of the program's exception: its text reaches the trace,
                    # or runs patched code, when the program replaced a hook or `sys.stderr`, or
                    # changed a stream or `io`.
                    if (hook is not default_unraisablehook or report_reaches_program() or
                            sys_vars.get("stderr") is not real_err):
                        cut_here()
                    at = len(data)
                    try:
                        call_hook(hook, UnraisableHookArgs((type(e), e, tb, None, threading)))
                    except BaseException:
                        # CPython then writes it with its own writer, which this script doesn't
                        # reproduce.
                        cuts.append(at)
                    del e, tb, hook
            del threading
            atexit._run_exitfuncs()
            # CPython's final flushes of a `sys.stdout` or `sys.stderr` that the program left in
            # place of the original ones run the program's code, which this script doesn't
            # reproduce.
            if (sys_vars.get("stdout") is not out or
                    sys_vars.get("stderr") is not real_err or report_reaches_program()):
                cut_here()
            flush(sys_vars.get("stdout"))  # as CPython does after the exit handlers
            check_unchanged("after the exit handlers")
            del kept
            # Rendering the globals runs no program code, but a thread of the program may still
            # print meanwhile; a write that reaches `sys.stdout` or the capture fails the trace.
            had_stdout, prog_out = "stdout" in sys_vars, sys_vars.get("stdout")
            # No collection while the sink is in place, so that no finalizer or gc callback writes
            # into it; the module's finalizers run below.
            collecting = gc.isenabled()
            gc.disable()
            try:
                sys_vars["stdout"] = sink = io.StringIO()
                written = writes[0]
                lines = globals_lines(globs, None if annotated else first_annotations)
                # The output so far is in `python FILE`'s order; the teardown's need not be.
                teardown_at = len(data)
                # With a cut, the trace is cut before the teardown anyway.
                teardown_runs = not cuts and runs_at_teardown(baseline, before, frozen)
                del baseline, before
                if had_stdout:
                    sys_vars["stdout"] = prog_out
                else:
                    del sys_vars["stdout"]
                del prog_out
            finally:
                if collecting:
                    gc.enable()
            if sink.getvalue() or writes[0] != written:
                fail(f"trace.py: a thread of {path} printed while its globals rendered")
            # As at the end of `python FILE`: the module's finalizers run while its globals are
            # intact.
            modules["__main__"] = real_main
            dunder = sys_vars.get("__stdout__")
            sys_vars["stdout"] = out if dunder is real_dunder else dunder
            sys_vars["stderr"] = sys_vars.get("__stderr__")  # as CPython restores it too
            del dunder
            # As CPython's finalization does: a collection, then the report's references to the
            # exception go, and with them the locals of its frames.
            gc.collect()
            for name in ("last_exc", "last_type", "last_value", "last_traceback"):
                sys_vars[name] = None
            del module, globs
            gc.collect()
            check_unchanged("after the teardown")
        finally:
            # This script's own messages go to file descriptor 2, also if the program closed or
            # dropped its `sys.stderr`.
            if getattr(real_err, "closed", True):
                real_err = open(2, "w", encoding="utf-8", errors="backslashreplace", closefd=False)
            sys_vars["stderr"] = real_err
            # The program is over: no later collection runs its finalizers or its gc callbacks.
            gc.disable()
            gc.callbacks.clear()
            sys_vars["stdout"] = real
            modules["__main__"] = real_main
            sys_vars["argv"] = real_argv
            sys_vars["path"][0] = real_path0
            sys_vars["__stdout__"] = real_dunder
            try:  # through its type, so that a `flush` that the program set on it doesn't run
                io.TextIOWrapper.flush(real_dunder)
            except Exception:
                pass
            os.dup2(real_fd1, 1)
            os.close(real_fd1)
        flush_own(out)
        if os.lseek(stray, 0, os.SEEK_END) > 0 or os.fstat(stray).st_ctime_ns != stray_changed:
            fail(f"trace.py: {path} wrote to file descriptor 1 outside sys.stdout")
        def mask(s):
            for p in paths:
                s = s.replace(p, tokens[p])
            return s

        try:
            text = mask(bytes(data).decode("utf-8"))
        except UnicodeDecodeError:  # a trace is UTF-8 text, so it can't hold such output
            fail(f"trace.py: {path} wrote bytes that aren't UTF-8")
        if "sys.addaudithook" in audited:
            fail(f"trace.py: {path} added an audit hook, which would also see this script's"
                     " code")
        if "os.fork" in audited or "os.forkpty" in audited:
            fail(f"trace.py: {path} forked, and a child's output doesn't reach the trace")
        sections = [f"--- stdout {len(text)}\n" + text, "--- outcome", *outcome, "--- globals",
                    *lines]
        if teardown_runs or cuts:
            # Only the output up to here is `python FILE`'s; SemDiff gives such a program a gap.
            ordered = min(cuts + [teardown_at])
            prefix = bytes(data[:ordered]).decode("utf-8", errors="ignore")
            # A path that the cut splits is masked in the whole text but not in the prefix, so the
            # prefix ends before the split path.
            split = max((k for p in paths for k in range(1, len(p)) if prefix.endswith(p[:k])),
                        default=0)
            sections.append(f"--- teardown after {len(mask(prefix[:len(prefix) - split]))}")
        trace = mask("\n".join(sections))
        try:
            encoded = (trace + "\n").encode("utf-8")
        except UnicodeEncodeError:  # a lone surrogate in the outcome or in a global's name
            fail(f"trace.py: the trace of {path} holds text that isn't UTF-8")
        # Straight to file descriptor 1, through this script's own `os`: no stream object, whose
        # methods the program may have shadowed, carries the trace.
        while encoded:
            encoded = encoded[os.write(1, encoded):]
    finally:
        os.chdir("/")
        # A directory that this cleanup can't remove is removed, or reported, by the next run.
        try:
            remove_tree(cwd)
        except Exception:
            pass
        os.close(lock)


if __name__ == "__main__":
    # The trace, or the failure's message, is this script's last act: `os._exit` ends the process
    # without running anything that the program left behind (a `threading` exit callback, a
    # finalizer, a stream's own `flush`), so that nothing reaches the output after it.  Both go
    # straight to their file descriptors, through no stream object.
    write, exit_now = os.write, os._exit
    status = 0
    try:
        main(sys.argv[1])
    except SystemExit as e:
        if type(e.code) is str:
            write(2, (e.code + "\n").encode("utf-8", "backslashreplace"))
            status = 1
        elif type(e.code) is int:
            status = e.code
    except BaseException as e:  # a bug of this script's
        write(2, f"trace.py: {qualname(type(e))}: {BaseException.__str__(e)}\n".encode(
            "utf-8", "backslashreplace"))
        status = 1
    exit_now(status)

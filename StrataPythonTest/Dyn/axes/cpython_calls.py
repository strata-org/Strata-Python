"""Record the built-in functions and methods that a grid program's case calls, for the coverage
check; this run's output is never compared with anything.

    python3.12 cpython_calls.py FILE.py

It runs FILE.py with a `sys.monitoring` hook on calls, and prints one name per line: the name of a
built-in function (`len`), `<type>.<name>` for a method of a built-in type, named by the type that
defines it (`str.split`, also for an instance of a subclass of `str`; `int.__add__` for
`(1).__add__`), and `<module>.<qualname>` for a Python function of `typing` or `dataclasses`. A
call counts only between the case's `_mark("op", …)` and `_mark("done", …)` calls, and only from
the program's module code or a class body that the program defines, not from its functions
(`show`, `_mark`, the user methods). Calls that the interpreter makes by itself, such as `__add__`
for `a + b`, are not seen; the catalog maps those to their entries.
"""

import dis
import io
import sys
import types

CO_OPTIMIZED = 0x1
WATCHED = ("typing", "dataclasses")
# The built-in classes with their own vectorcall in CPython 3.12 (`float_vectorcall`,
# `tuple_vectorcall`, …).
OWN_CALL_NEW_ONLY = (float, tuple, bool, frozenset, range, enumerate, reversed)
OWN_CALL_NEW_INIT = (list, dict, set)
TOOL = sys.monitoring.PROFILER_ID


def defining(cls, name):
    """`<type>.<name>` for the built-in type in the MRO of `cls` that defines `name`."""
    for c in cls.__mro__:
        if name in vars(c) and c.__module__ == "builtins":
            return f"{c.__qualname__}.{name}"
    return f"{cls.__qualname__}.{name}"


def name_of(f, nargs):
    """The coverage name of the callable `f` called with `nargs` arguments, a list of names for a
    built-in class, or `None` for one that the check doesn't track."""
    kind = type(f).__name__
    if kind == "builtin_function_or_method":
        self = f.__self__
        if self is None or isinstance(self, types.ModuleType):
            mod = getattr(f, "__module__", None) or "builtins"
            # A static method of a built-in type (`str.maketrans`) has its type in its qualified
            # name.
            return f.__qualname__ if mod == "builtins" else f"{mod}.{f.__qualname__}"
        return defining(self if isinstance(self, type) else type(self), f.__name__)
    if kind == "method-wrapper":
        return defining(type(f.__self__), f.__name__)
    if kind in ("wrapper_descriptor", "method_descriptor", "classmethod_descriptor"):
        return defining(f.__objclass__, f.__name__)
    if isinstance(f, type) and f.__module__ == "builtins":
        # `type(x)` returns the type at once (`type_vectorcall`) and runs none of them.
        if f is type and nargs == 1:
            return None
        # These classes have their own vectorcall in 3.12, which runs their `__new__` code
        # (and, for `list`, `dict` and `set`, their `__init__` code) without `type.__call__`.
        if f in OWN_CALL_NEW_ONLY:
            return [defining(f, "__new__")]
        if f in OWN_CALL_NEW_INIT:
            return [defining(f, "__new__"), defining(f, "__init__")]
        # A call of another built-in class runs its `__new__` and `__init__` through
        # `type.__call__`, named by the type that defines them.
        return [defining(f, "__new__"), defining(f, "__init__"), "type.__call__"]
    if kind in ("function", "method"):
        fn = getattr(f, "__func__", f)
        mod = getattr(fn, "__module__", "")
        if mod in WATCHED:
            return f"{mod}.{fn.__qualname__}"
    return None


def main(path):
    with open(path, encoding="utf-8") as f:
        code = compile(f.read(), path, "exec")
    names = set()
    state = {"on": False}
    nargs_at = {}

    def nargs(caller, offset):
        """The argument count of the `CALL` instruction at `offset` of `caller`."""
        if caller not in nargs_at:
            nargs_at[caller] = {i.offset: i.arg for i in dis.get_instructions(caller)
                                if i.opname == "CALL"}
        return nargs_at[caller].get(offset)

    def on_call(caller, offset, callable_, arg0):
        if getattr(callable_, "__name__", None) == "_mark" and \
                getattr(callable_, "__code__", None) is not None and \
                callable_.__code__.co_filename == path:
            state["on"] = arg0 == "op"
            return
        if state["on"] and caller.co_filename == path and not (caller.co_flags & CO_OPTIMIZED):
            n = name_of(callable_, nargs(caller, offset))
            if isinstance(n, list):
                names.update(n)
            elif n is not None:
                names.add(n)

    module = types.ModuleType("__main__")
    real = sys.stdout
    sys.stdout = io.StringIO()
    sys.monitoring.use_tool_id(TOOL, "grid coverage")
    sys.monitoring.register_callback(TOOL, sys.monitoring.events.CALL, on_call)
    sys.monitoring.set_events(TOOL, sys.monitoring.events.CALL)
    try:
        exec(code, module.__dict__)
    except BaseException:  # the program's own exception; only its calls matter here
        pass
    finally:
        sys.monitoring.set_events(TOOL, 0)
        sys.monitoring.free_tool_id(TOOL)
        sys.stdout = real
    for n in sorted(names):
        print(n)


if __name__ == "__main__":
    main(sys.argv[1])

# Test: raise from None, the errors of ExceptionGroup and add_note, and the read-only message
def run(name, f):
    try:
        f()
    except Exception as e:
        print(name, type(e).__name__, e.args[0])
try:
    try:
        raise KeyError("k")
    except KeyError:
        raise ValueError("v") from None
except ValueError as e:
    print(e.__cause__, e.__suppress_context__, type(e.__context__) is KeyError)
run("eg msg", lambda: ExceptionGroup(1, [ValueError()]))
run("eg seq", lambda: ExceptionGroup("m", 5))
run("eg empty", lambda: ExceptionGroup("m", []))
run("eg item", lambda: ExceptionGroup("m", [1]))
run("eg nest", lambda: ExceptionGroup("m", [KeyboardInterrupt()]))
g = ExceptionGroup("m", [ValueError(1)])
def wmsg():
    g.message = "n"
run("eg message", wmsg)
e = ValueError()
run("note type", lambda: e.add_note(1))
e.__notes__ = 5
run("note list", lambda: e.add_note("x"))
run("init kw", lambda: ValueError(x=1))
run("os kw", lambda: OSError(1, "a", k=2))

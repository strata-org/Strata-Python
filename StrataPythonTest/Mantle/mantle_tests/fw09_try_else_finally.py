# try/except/else/finally: the except clauses do not cover the else body, the finally covers
# every part, and a try body that leaves early skips the else.
import sys

log = []

def note(x):
    log.append(x)
    return x

def else_raises():
    try:
        note("body")
    except KeyError:
        note("clause")  # not run: the else body's KeyError is not caught here
    else:
        raise KeyError("else")
    finally:
        note(sys.exc_info()[1])  # the pending KeyError('else')

def clause_raises():
    try:
        raise KeyError("body")
    except KeyError:
        raise ValueError("clause")  # its __context__ is the KeyError
    else:
        note("else")
    finally:
        note(sys.exc_info()[1])  # the pending ValueError

def leaves_early(xs):
    for x in xs:
        try:
            if x == 1:
                break  # skips the else, runs the finally
            if x == 2:
                return "body"  # skips the else too
        except KeyError:
            pass
        else:
            note("else")  # runs only when the try body ends normally
        finally:
            note(x)
    return "after"

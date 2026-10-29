# try/except/else: matching clauses, binding the exception, and leaving a handler.
def clauses(f):
    try:
        f()
    except (KeyError, IndexError):
        return 1
    except ValueError as e:
        return e
    except:
        return 3
    else:
        return 4

def no_match(f):
    try:
        f()
    except KeyError:
        pass
    return 0

def leave(xs, f):
    for x in xs:
        try:
            f(x)
        except KeyError as e:
            continue
        except ValueError:
            break
    return x

def nested(f):
    try:
        f()
    except KeyError:
        try:
            f()
        except ValueError:
            raise
        raise

def in_inner_body(f):
    try:
        f()
    except KeyError:
        try:
            raise
        except ValueError:
            pass

def clause_raises(f):
    try:
        f()
    except KeyError as e:
        f(e)

def closure(f):
    try:
        f()
    except KeyError as e:
        def g():
            return e
        return g

def two_handlers(f):
    try:
        f()
    except KeyError as a:
        try:
            f()
        except ValueError as b:
            return a, b

def not_inherited(f):
    try:
        f()
    except KeyError:
        def g():
            raise
        class D:
            raise

def finally_raise(f):
    try:
        raise KeyError("outer")
    except KeyError:
        try:
            f()
        finally:
            raise  # what f raised; if f returns, KeyError("outer")

class C:
    try:
        pass
    except Exception as err:
        pass
    for x in [1, 2]:
        try:
            raise KeyError
        except KeyError as e:
            break

try:
    pass
except Exception as top:
    pass

try:
    pass
finally:
    pass

try:
    pass
except* ValueError:
    pass

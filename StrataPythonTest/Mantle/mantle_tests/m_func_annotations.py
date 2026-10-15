# Parameter and return annotations: evaluated at the def, in the enclosing scope, after the
# defaults, and stored in the function's __annotations__ before the decorators run.
log = []

def note(x):
    log.append(x)
    return x

def keys(f):
    note(list(f.__annotations__))  # the annotations are there when a decorator runs
    return f

@keys
def ordered(p: note("p"), /, a: note("a") = note("default"), *v: note("v"), k: note("k"),
            **kw: note("kw")) -> note("return"):
    pass  # log: default, a, p, v, k, kw, return; keys: a, p, v, k, kw, return

def plain(x, y=1):
    return x  # no annotations: __annotations__ is an empty dict

def enclosing():
    T = int
    def f(x: T) -> T:  # T is enclosing's local, read when f is defined
        return x
    return f

class K:
    def m(self, __x: int, *, __y: str) -> None:  # keys _K__x and _K__y
        pass

def outer():
    T = int
    def mid():
        def inner(x: T):  # mid captures T only for this annotation
            pass
        return inner
    return mid

class C:
    __T = int
    def m(self, x: __T):  # reads _C__T
        pass

# The symbol table visits the decorators before the annotations, and the positional-only
# annotations before the positional ones; the lambdas' order in .symtable pins both.
@note(lambda a: a)
def scopes(x: (lambda b: b)):
    pass

def scopes_positional(p: (lambda c: c), /, q: (lambda d: d)):
    pass

# The symbol table visits the **kwargs annotation before the keyword-only ones, unlike
# evaluation; the lambdas' order in .symtable pins it.
def scopes_keyword(*, k: (lambda e: e), **kw: (lambda f: f)):
    pass

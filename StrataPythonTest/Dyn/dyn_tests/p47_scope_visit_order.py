# Names that appear only inside a `match` pattern, a guard, a dict key or an annotation.
def patterns(cmd):
    match cmd:
        case Color.RED:
            pass
        case {Keys.A: v}:
            pass
        case Point(Origin.X, y=Kind.B):
            pass
        case [Shape.SQUARE, *_] | (Shape.CIRCLE, *_):
            pass
        case n if LIMIT > n:
            pass


def keys():
    return {KEY_ONLY: 1}


def annotated(p: (lambda a: a), *v: (lambda b: b), k: (lambda c: c), **kw: (lambda d: d)):
    pass

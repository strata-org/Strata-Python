"""Reference functions for the probes of the contract operations whose docstrings differ from the
Python they stand for.  Each follows its operation's docstring in `StrataPython/Dyn/Env.lean`
with CPython's own data, so that a probe never compares the model with its own output."""


def is_exact_str(k):
    return type(k) is str


def argOf_ref(args, kwargs, pos, name, default):
    """`args[pos]` if `args` is exactly a tuple and `pos` is in range, else the value of the key of
    `kwargs` that is exactly the `str` `name`, if `kwargs` is exactly a dict, else `default`."""
    if type(args) is tuple and 0 <= pos < tuple.__len__(args):
        return tuple.__getitem__(args, pos)
    if type(kwargs) is dict:
        for k, v in dict.items(kwargs):
            if is_exact_str(k) and str.__eq__(k, name):
                return v
    return default


def extraKwargs_ref(kwargs, names):
    """A new dict of the entries of `kwargs`, but those whose key is exactly a `str` among `names`;
    an empty dict if `kwargs` is not exactly a dict."""
    if type(kwargs) is not dict:
        return {}
    return {k: v for k, v in dict.items(kwargs) if not (is_exact_str(k) and k in names)}


def bindsTo_ref(args, kwargs, n_pos, var_kw, names):
    """Whether binding `args` and `kwargs` to the parameters `names`, of which the first `n_pos`
    may be given by position, raises none of the docstring's `TypeError`s."""
    if type(args) is not tuple or type(kwargs) is not dict:
        return False
    keys = list(dict.keys(kwargs))
    if not all(is_exact_str(k) for k in keys):
        return False
    if n_pos < 0 or n_pos > len(names) or len(args) > n_pos:
        return False
    positional = names[:len(args)]
    if any(k in positional for k in keys):
        return False
    if not var_kw and not all(k in names for k in keys):
        return False
    return True


MESSAGE = "typeIsSubclass() arg 2 must be a class or a tuple of classes"


def typeIsSubclass_ref(v, cls):
    """Whether the stored MRO of `type(v)` holds `cls`, or one class of the flat tuple `cls`; a
    `TypeError` if `cls` is neither, every element checked first."""
    cs = cls if type(cls) is tuple else (cls,)
    for c in cs:
        if not issubclass(type(c), type):
            raise TypeError(MESSAGE)
    mro = type.__dict__["__mro__"].__get__(type(v))
    return any(t is c for c in cs for t in mro)


def strIsOneOf_ref(v, lits):
    return is_exact_str(v) and v in lits


def intIsOneOf_ref(v, lits):
    return type(v) is int and v in lits


def isImmutableScalar_ref(v):
    return type(v) in (int, float, complex, bool, str, bytes, type(None))


def dictKeysWithin_ref(d, keys):
    return type(d) is dict and all(is_exact_str(k) and k in keys for k in dict.keys(d))


def binds(f, args, kwargs):
    """Whether CPython binds `args` and `kwargs` to the parameters of `f` without a `TypeError`."""
    try:
        f(*args, **kwargs)
        return True
    except TypeError:
        return False


def builtin(name):
    """The value of `name` in the module `builtins`, whatever the program binds `name` to."""
    import builtins
    return getattr(builtins, name)


def reSearch_ref(pattern, s):
    """Whether `re.search(pattern, s)` finds a match, with the standard library's `re`."""
    import re
    return re.search(pattern, s) is not None


def type_name(v):
    """The `__name__` of `type(v)`, read without a metaclass's `__name__` property."""
    return type.__dict__["__name__"].__get__(type(v))


def members_ref(c, op):
    """The members that the quantifier `op` reads: the stored elements of a list or tuple, the
    members of a set or frozenset, or the keys of a dict, read with the base class's own methods,
    so that an overridden `__iter__` is not used.  A `TypeError` for any other `c`."""
    for base in (list, tuple, set, frozenset, dict):
        if issubclass(type(c), base):
            return tuple(base.__iter__(c))
    raise TypeError(f"{op}() argument must be a list, tuple, set, frozenset or dict, "
                    f"not '{type_name(c)}'")


def allIn_ref(c, pred):
    """Whether `pred` is true for every member of `c`: every member runs, in order, and the first
    exception propagates with its own context."""
    results = [bool(pred(x)) for x in members_ref(c, "allIn")]
    return all(results)


def anyIn_ref(c, pred):
    results = [bool(pred(x)) for x in members_ref(c, "anyIn")]
    return any(results)


def items_ref(d, op):
    if not issubclass(type(d), dict):
        raise TypeError(f"{op}() argument must be a dict, not '{type_name(d)}'")
    return tuple(dict.items(d))


def allItems_ref(d, pred):
    results = [bool(pred(k, v)) for k, v in items_ref(d, "allItems")]
    return all(results)


def anyItems_ref(d, pred):
    results = [bool(pred(k, v)) for k, v in items_ref(d, "anyItems")]
    return any(results)

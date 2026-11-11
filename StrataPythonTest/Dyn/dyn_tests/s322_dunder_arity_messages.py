# The argument errors of a slot wrapper that takes no argument (an exception's __str__ and __repr__), of
# the repetition wrappers (__mul__, __rmul__, __imul__), and of the dunders that CPython defines as
# methods (list.__getitem__, dict.__getitem__, dict.__contains__ and set.__contains__).
try:
    BaseException().__repr__(1)
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    BaseException().__repr__(x=1)
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    BaseException().__str__(1)
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    ValueError('x').__str__(1)
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    {}.__contains__()
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    {}.__getitem__()
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    [].__getitem__()
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    [1].__getitem__(0, 1)
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    [].__getitem__(0, x=1)
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    BaseExceptionGroup('m', [ValueError()]).__str__(1)
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    ImportError().__str__(1)
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    KeyError().__str__(1)
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    NameError().__str__(1)
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    OSError().__str__(1)
    print('ok')
except Exception as e:
    print(type(e).__name__, e)
try:
    {2}.__contains__()
except TypeError as e:
    print(e)
try:
    {3}.__contains__(1, 2)
except TypeError as e:
    print(e)
for call in [lambda: [1].__mul__(), lambda: "a".__rmul__(1, 2), lambda: [].__imul__(),
             lambda: (1,).__mul__(2, x=1)]:
    try:
        call()
    except TypeError as e:
        print(repr(e.args[0]))

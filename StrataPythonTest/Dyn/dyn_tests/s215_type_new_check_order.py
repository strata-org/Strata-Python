# Test: the checks of type.__new__ on bases and __slots__, in CPython's order
def make(f):
    try:
        f()
        print("made")
    except (TypeError, ValueError) as e:
        print(type(e).__name__, e.args[0])
def dict_twice():
    class X:
        __slots__ = ('__dict__', '__dict__')
def not_identifier():
    class X:
        __slots__ = ('1a', 2)
def int_subtype():
    class Y(int):
        __slots__ = ('1a',)
class I(int):
    pass
def int_subclass_subtype():
    class J(I):
        __slots__ = ('a',)
class A:
    pass
class S:
    __slots__ = ()
def dict_from_second_base():
    class C(S, A):
        __slots__ = ('__dict__',)
class B(A):
    pass
def item_before_mro():
    class C(A, B):
        __slots__ = (1,)
def layout_conflict():
    class D(int, str, bool):
        pass
def qualname_slot():
    class X:
        __slots__ = ('__qualname__',)
for f in (dict_twice, not_identifier, int_subtype, int_subclass_subtype, dict_from_second_base,
          item_before_mro, layout_conflict, qualname_slot):
    make(f)

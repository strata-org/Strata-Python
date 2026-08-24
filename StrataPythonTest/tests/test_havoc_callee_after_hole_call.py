# strata-args: --check-mode bugFinding --check-level full
class MyClass:
    def __init__(self, n: int):
        self.val : int = n

xs: list[int] = [1, 2]
xs.some_unmodeled_call_1(3)
assert xs == [1, 2], "expected unknown because xs should be havocked"

xs = [1,2]
ys: list[int] = xs.some_unmodeled_call_2()
assert xs == [1, 2], "expected unknown because xs should be havocked"

xs = [1,2]
xs.some_unmodeled_call_3.some_unmodeled_call_4()
assert xs == [1, 2], "chained call: receiver not havocked (chained attribute is not a Name)"

xs = [1,2]
some_function().some_unmodeled_call_5()
assert xs == [1, 2], "unrelated variable: nothing should be havocked"

a : MyClass = MyClass(2)
a.val = 1
some_unmodeled_call_6(a)
assert a.val == 1, "composite arg: heap not havocked (out of scope)"

xs2: list[int] = [1, 2]
ys2: list[int] = []
xs2.unknown_method_that_may_modify_arguments(ys2)
assert ys2 == [], "expected unknown because argument locals should be havocked"

# Regression: unmodeled method call as for-loop iterator.
# The receiver havoc must be lifted out of the iterator expression so
# the block does not end up in expression position inside the assume.
response: dict = {"messages": []}
for msg in response.unmodeled_iter_method():
    assert True, "for-loop over unmodeled iterator should not crash"

# Module globals use static fields rather than local declarations, but unknown
# calls can mutate their reachable values in exactly the same ways.
global_receiver: list[int] = [1, 2]
global_receiver.some_unmodeled_call_7()
assert global_receiver == [1, 2], "module-global receiver should be havocked"

global_arg: list[int] = [1, 2]
some_unmodeled_call_8(global_arg)
assert global_arg == [1, 2], "module-global positional argument should be havocked"

global_kwarg: list[int] = [1, 2]
some_unmodeled_call_9(value=global_kwarg)
assert global_kwarg == [1, 2], "module-global keyword argument should be havocked"

global_nested: dict = {"items": []}
global_nested["items"].some_unmodeled_call_10()
assert global_nested == {"items": []}, "module-global reachable receiver should be havocked"

global_wrapped: list[int] = [1, 2]
some_unmodeled_call_11([global_wrapped])
assert global_wrapped == [1, 2], "module-global root in aggregate should be havocked"

global_conditional: list[int] = [1, 2]
some_unmodeled_call_12(global_conditional if True else [])
assert global_conditional == [1, 2], "module-global root in conditional should be havocked"


def havoc_kwargs(**kwargs):
    some_unmodeled_call_13(kwargs)
    assert kwargs == {"value": [1, 2]}, "kwargs should be havocked"


havoc_kwargs(value=[1, 2])

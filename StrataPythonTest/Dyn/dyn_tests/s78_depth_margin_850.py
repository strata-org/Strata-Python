# Test: == of lists nested 7000 deep around dicts with a tuple key nested 890 deep, in 850 nested class calls
def nest_list(n, inner):
    x = inner
    i = 0
    while i < n:
        x = [x]
        i = i + 1
    return x
def nest_tuple(n):
    x = ()
    i = 0
    while i < n:
        x = (x,)
        i = i + 1
    return x
a = nest_list(7000, {nest_tuple(890): 1})
b = nest_list(7000, {nest_tuple(890): 1})
class C:
    def __init__(self, k):
        if k > 0:
            C(k - 1)
        else:
            print(a == b)
C(850)
del a
del b
print("done")

# str.maketrans: two or three strs, or a dict whose str keys become code points, and its errors.
def show(f, *args):
    try:
        print(repr(f(*args)))
    except (TypeError, ValueError) as e:
        print(type(e).__name__, e.args[0])


print("abc".translate(str.maketrans("ab", "xy", "c")))
print(str.maketrans("ab", "cd"), str.maketrans({"a": 1, 98: "x", "c": None}))
print(str.maketrans("ab", "cd", "e"), "".maketrans("", ""))
show(str.maketrans, 1)
show(str.maketrans, {1.5: 1})
show(str.maketrans, "ab", "c")
show(str.maketrans, "a", 1)
show(str.maketrans, {"ab": 1})
show(str.maketrans, "a", "b", 1)
show(str.maketrans, 1, "b")

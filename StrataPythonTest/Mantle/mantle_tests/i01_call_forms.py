# Every call-site argument form: positional, keyword, *args, **kwargs, and mixes.
def show(*args, **kwargs):
    print(len(args), args)
    print(len(kwargs), kwargs)

show()
show(1, 2)
show(k=1, j=2)
show(1, k=2)

xs = [1, 2, 3]
show(*xs)
show(*xs, *xs)
show(0, *xs, 4)

m = {"a": 1, "b": 2}
show(**m)
show(x=0, **m)
show(**m, **{"c": 3})
show(1, *xs, 9, k=0, **m, **{"d": 4})

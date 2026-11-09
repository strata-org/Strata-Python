# Test: an unbound call of a built-in's __new__ or method checks its first argument before the body runs
try:
    tuple.__new__(zip, [1, 2])
except TypeError as e:
    print(e.args[0])
try:
    list.extend((1,), [2])
except TypeError as e:
    print(e.args[0])

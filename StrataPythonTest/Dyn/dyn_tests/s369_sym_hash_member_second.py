# Test: a list holding a tuple, compared with a list holding an int whose number the model does
# not know (a hash), stops with the gap of the number comparison
a = "a".__hash__()
print([(1,)] == [a])

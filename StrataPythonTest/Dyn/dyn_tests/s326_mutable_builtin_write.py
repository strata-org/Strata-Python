# A built-in type refuses an attribute write or deletion, naming the type by its C name, but
# CPython 3.12 doesn't mark six of them, such as ExceptionGroup, immutable, so it stores the write;
# the model doesn't follow that write, so it stops with a gap.
try:
    int.x = 1
except TypeError as e:
    print(e)
try:
    del int.x
except TypeError as e:
    print(e)
try:
    type(len).x = 1
except TypeError as e:
    print(e)
ExceptionGroup.x = 1
print(ExceptionGroup.x)

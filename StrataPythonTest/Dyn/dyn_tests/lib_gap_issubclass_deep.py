# issubclass over tuples nested deeper than the model follows stops with a gap.
t = str
for i in range(200):
    t = (t,)
print(issubclass(str, t))

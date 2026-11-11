# A union of 200 classes: its == and | scan the arguments pairwise, which takes the model
# time quadratic in the width (CPython's == is linear).
classes = []
for i in range(200):
    classes.append(type(f"C{i}", (), {"__module__": "__main__"}))
u = classes[0]
for c in classes[1:]:
    u = u | c
v = classes[-1]
for c in reversed(classes[:-1]):
    v = v | c
print(len(u.__args__), u == v, u != (v | int), len((u | int).__args__))

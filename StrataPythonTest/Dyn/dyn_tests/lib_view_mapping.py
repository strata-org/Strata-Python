# A dict view's mapping is a read-only proxy of its dict, which reads the dict as it is now.
d = {1: "a"}
m = d.keys().mapping
print(m[1], d.items().mapping[1], d.values().mapping[1])
d[2] = "b"
print(m[2])
try:
    m[3]
except KeyError as e:
    print("KeyError", e)

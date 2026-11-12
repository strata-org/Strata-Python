# Updating an existing str key through an equal non-str key converts the table in CPython, which
# compacts the entries while the loop walks them; the model stops with a gap.
class K:
    def __hash__(self):
        return "q".__hash__()
    def __eq__(self, o):
        return o == "q"
a = {"x": 0, "p": 1, "q": 2, "r": 3}
del a["x"]
for k in a:
    print(k)
    if k == "p":
        a[K()] = 5
print(a)

# Test: the characters that a str iterator gives, over a str with characters of 1 to 4 bytes
s = "aé€😀b"
it = iter(s)
print(next(it), next(it))
it2 = iter(s)
print(next(it2), next(it), it.__length_hint__())
for c in s:
    print(c)
print(next(it), next(it2), next(it, "end"), type(it).__name__)

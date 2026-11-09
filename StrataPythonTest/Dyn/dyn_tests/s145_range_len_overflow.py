# Test: len() and __len__ of a range longer than a Py_ssize_t raise OverflowError
for t in [lambda: len(range(2**70)), lambda: range(2**70).__len__(), lambda: len(range(2**63 - 1)), lambda: len(range(2**63))]:
    try:
        print(t())
    except OverflowError as e:
        print("OverflowError", e.args[0])
it = iter(range(2**70))
print(it.__length_hint__() == 2**70)

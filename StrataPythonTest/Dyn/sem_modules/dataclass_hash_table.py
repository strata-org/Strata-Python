# The 16 rows of dataclasses' _hash_action table.
from dataclasses import dataclass
for unsafe_hash in (False, True):
    for eq in (False, True):
        for frozen in (False, True):
            for explicit in (False, True):
                try:
                    ns = {"__module__": "__main__", "__annotations__": {"a": int}}
                    if explicit:
                        ns["__hash__"] = lambda self: 42
                    C = type("C", (), ns)
                    C = dataclass(unsafe_hash=unsafe_hash, eq=eq, frozen=frozen)(C)
                    try:
                        h = C.__dict__["__hash__"]
                    except KeyError:
                        h = "absent"
                    kind = "none" if h is None else "absent" if h == "absent" else "explicit" if explicit and h(C(1)) == 42 else "fields" if h(C(1)) == (1,).__hash__() else "other"
                    print(unsafe_hash, eq, frozen, explicit, kind)
                except TypeError as e:
                    print(unsafe_hash, eq, frozen, explicit, "TypeError:", e)

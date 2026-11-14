from dataclasses import dataclass
for f in ("order_no_eq", "frozen_inherit", "overwrite_lt"):
    try:
        if f == "order_no_eq":
            @dataclass(order=True, eq=False)
            class A:
                a: int
        elif f == "frozen_inherit":
            @dataclass(frozen=True)
            class B:
                a: int
            @dataclass
            class C(B):
                b: int = 0
        else:
            @dataclass(order=True)
            class E:
                a: int
                def __lt__(self, o):
                    return True
        print(f, "ok")
    except (TypeError, ValueError) as e:
        print(f, type(e).__name__, e)

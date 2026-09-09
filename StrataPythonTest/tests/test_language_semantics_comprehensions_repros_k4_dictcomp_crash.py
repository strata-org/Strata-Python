# Minimal repro: dict comprehension + tuple destructuring + str values
# -> Invariant check failed, src/util/simplify_expr.cpp:3422, simplify_rec
def main() -> None:
    d = {k: v for k, v in [(1, "a"), (2, "b")]}
    assert len(d) == 2
main()

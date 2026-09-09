# K1 dictclash
def main() -> None:
    src = [1, 2, 1]                      # duplicate key source, CONCRETE
    d = {k: k * 10 for k in src}
    assert len(d) == 2                   # Python: 2 (dedup). Wrong model -> 3
main()

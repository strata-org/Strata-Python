# K3 tuple nodup
def main() -> None:
    d = {k: v for k, v in [(1, 'a'), (2, 'b')]}   # tuple target, NO duplicate
    assert len(d) == 2
main()

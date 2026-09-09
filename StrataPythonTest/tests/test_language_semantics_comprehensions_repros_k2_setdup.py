# K2 setdup
def main() -> None:
    src = [1, 2, 1]
    s = {x for x in src}
    assert len(s) == 2                   # Python: 2. List-routed model -> 3
main()

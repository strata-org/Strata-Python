class B:
    def __getattr__(self, name: str) -> int:
        assert len(name) >= 3, "long names only"

class C(B):
    pass

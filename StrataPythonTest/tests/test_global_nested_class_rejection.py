state: int = 0


class Outer:
    class Inner:
        global state
        state = 1

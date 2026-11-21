# strata-args: --check-mode bugFinding --check-level full
# User functions are opaque: main knows CircularBuffer@__init__ only through
# its contract, not through its body, which is not inlined into main. This
# test pins that contract-only behaviour: the checks reported at the call are
# the preconditions of __init__.
#
import test_helper

class CircularBuffer:
    name: str
    def __init__(self, size: int, name: str):
        self.size: int = size
        self.name = name

def main():
    my_buf: CircularBuffer = CircularBuffer(5, "circbuff")
    print("Bye")

if __name__ == "__main__":
    main()

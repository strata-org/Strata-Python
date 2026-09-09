# Attribute access modeled as static field read; CPython uses 4-step protocol
# with fallthrough to __getattr__
"""
Demonstrates the 4-step attribute access protocol fallthrough.
After del self.x, access falls to __getattr__ which returns wrong type.
"""

class Fallback:
    def __init__(self) -> None:
        self.x: int = 42

    def __getattr__(self, name: str) -> str:
        return "fallback"

    def clear(self) -> None:
        del self.x

def main() -> None:
    f = Fallback()
    print(f.x)        # 42 (step 2: instance __dict__)
    f.clear()         # removes x from __dict__
    print(f.x)        # "fallback" (step 4: __getattr__)
    result = f.x - 1  # TypeError: str - int

main()

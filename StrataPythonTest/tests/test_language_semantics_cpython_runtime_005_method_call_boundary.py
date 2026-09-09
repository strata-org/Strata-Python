# Method call: boundary case. Monkey-patching a method after class definition
# makes static resolution unsound.
"""Method call: boundary case.
Monkey-patching a method after class definition makes static resolution unsound.
"""

class Greeter:
    def greet(self) -> str:
        return "hello"

if __name__ == "__main__":
    g = Greeter()
    print(g.greet())  # hello -- model agrees

    # Monkey-patch the method
    Greeter.greet = lambda self: "goodbye"
    print(g.greet())  # goodbye -- model would still predict "hello"

# zero-arg super() relies on implicit __class__ cell
class Animal:
    def speak(self): return "..."
class Dog(Animal):
    def speak(self): return f"Woof! (parent: {super().speak()})"
assert Dog().speak() == "Woof! (parent: ...)"
print("OK: __class__ cell synthesis — super() works")

# Binary operators: boundary case. Monkey-patching __add__ makes the
# simplified model unsound. The static axiom 'int + int -> int' would be wrong
# after patching.
"""Binary operators: boundary case.
Monkey-patching __add__ makes the simplified model unsound.
The static axiom 'int + int -> int' would be wrong after patching.
"""

class MyInt:
    def __init__(self, val: int):
        self.val = val

    def __add__(self, other: 'MyInt') -> 'MyInt':
        return MyInt(self.val + other.val)

    def __repr__(self):
        return f"MyInt({self.val})"

# A simplified model would axiomatize: MyInt + MyInt -> MyInt(self.val + other.val)
a = MyInt(1)
b = MyInt(2)
print(a + b)  # MyInt(3) -- model agrees

# Now monkey-patch __add__ to do multiplication instead
MyInt.__add__ = lambda self, other: MyInt(self.val * other.val)
print(a + b)  # MyInt(2) -- model would predict MyInt(3), WRONG

# Decorators compose correctly: inner applied first
def add_greeting(f):
    def wrapper(name): return f"Hello, {f(name)}!"
    return wrapper
def uppercase(f):
    def wrapper(name): return f(name).upper()
    return wrapper

@add_greeting   # applied second (outer)
@uppercase      # applied first (inner)
def greet(name): return name

assert greet("world") == "Hello, WORLD!"
print("OK: decorator order — inner first, outer wraps it")

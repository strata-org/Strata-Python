# Iteration: boundary case. A generator with side effects and non-
# deterministic length cannot be modeled as a simple bounded loop.
"""Iteration: boundary case.
A generator with side effects and non-deterministic length
cannot be modeled as a simple bounded loop.
"""
import random

def flaky_generator():
    """Yields a random number of items with side effects."""
    count = random.randint(1, 5)
    for i in range(count):
        print(f"yielding {i}")  # side effect
        yield i * 2

def consume(gen) -> list:
    result = []
    for x in gen:
        result.append(x)
    return result

if __name__ == "__main__":
    # Length unknown at verification time, side effects in __next__
    result = consume(flaky_generator())
    print(result)  # e.g. [0, 2, 4] -- non-deterministic

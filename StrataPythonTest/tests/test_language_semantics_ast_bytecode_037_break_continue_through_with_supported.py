# Continue through with: __exit__ called each iteration.
"""Continue through with: __exit__ called each iteration."""
exit_count = 0
class CM:
    def __enter__(self): return self
    def __exit__(self, *a):
        global exit_count
        exit_count += 1
        return False

for i in range(3):
    with CM():
        if i % 2 == 0:
            continue

assert exit_count == 3  # __exit__ called for every iteration, including continues
print('PASS')

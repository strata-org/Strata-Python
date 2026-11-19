# Loop records.  `while True: pass` has a `done`: its test is not folded, and `py.truthy` can
# raise.  A module-level loop with a `try`/`finally` inside has a `done` whose return arm is
# unreachable.
def spin():
    while True:
        pass


for x in range(3):
    try:
        print(x)
    finally:
        print("done")

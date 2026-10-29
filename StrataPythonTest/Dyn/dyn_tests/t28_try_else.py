# Test: try/else — the else clause runs only on the normal (no-exception) path
# and is NOT protected by the try's handlers. Also exercises a nested try in the
# body to confirm the outer exceptional edge is restored after the inner try.

def risky():
    pass

def cleanup():
    pass

# try/except/else: else runs only when the body did not raise
try:
    x = risky()
except ValueError:
    x = 0
else:
    y = x

# try/except/else/finally
try:
    a = risky()
except:
    a = 1
else:
    b = a
finally:
    cleanup()

# Nested try in the body of an outer try: after the inner try completes, the
# outer handler must still cover the following call.
try:
    try:
        inner = risky()
    except ValueError:
        inner = 0
    outer = risky()
except:
    outer = -1

# Test: try/except/else/finally interleaved with for/while loops, inside and out,
# plus nested loops and explicit StopIteration.
#
# The focus is the exception edges around loop termination. Normal loop
# exhaustion is an implicit StopIteration in Python semantics, so three things
# must stay distinct:
#   1. a loop's own termination edge (goes to the loop's else / exit),
#   2. a StopIteration raised inside the body by user code (`next`, `raise`),
#      which an enclosing `except StopIteration` may catch,
#   3. an exception edge inherited from an enclosing try.
# An inner loop's exhaustion must also terminate only the inner loop.

def probe(x):
    return x

def check(x):
    return x

def cleanup():
    pass

def note(tag):
    return tag

def raiser():
    raise StopIteration

outer_items = [1, 2, 3]
inner_items = [4, 5]

# --- 1. Loop inside try/except/else/finally -----------------------------------
# Loop exhaustion must reach `else`, not the handler: the implicit StopIteration
# of the `for` is not an exception visible to `except KeyError`.
try:
    for a in outer_items:
        probe(a)
except KeyError:
    note(1)
else:
    note(2)
finally:
    cleanup()

# --- 2. try/except/else/finally inside the loop body -------------------------
# `continue` from the handler must still run `finally` before jumping back to
# the loop header.
for b in outer_items:
    try:
        probe(b)
    except ValueError:
        note(3)
        continue
    else:
        note(4)
    finally:
        cleanup()

# --- 3. break out of a try with finally; for/else must be skipped ------------
for c in outer_items:
    try:
        if check(c):
            break
    finally:
        cleanup()
else:
    note(5)

# --- 4. Nested loops: inner exhaustion and inner break are inner-only --------
for d in outer_items:
    for e in inner_items:
        try:
            probe(e)
        except IndexError:
            break
    else:
        note(6)
    note(7)

# --- 5. User-visible StopIteration inside a for body -------------------------
# The crux: `next` may raise StopIteration, which is caught here by the handler.
# It must not be confused with the enclosing `for`'s own termination edge.
manual = iter(inner_items)
for f in outer_items:
    try:
        g = next(manual)
    except StopIteration:
        note(8)
        break
    else:
        probe(g)

# --- 6. StopIteration from a called function, crossing a finally -------------
for m in outer_items:
    try:
        raiser()
    except StopIteration:
        note(9)
        continue
    finally:
        cleanup()

# --- 7. while/else with try/finally in the body ------------------------------
k = 0
while k < 3:
    try:
        probe(k)
    except TypeError:
        note(10)
    finally:
        k = k + 1
else:
    note(11)

# --- 8. try/finally around nested loops, with the break-outer idiom ---------
# `for/else` + `continue`/`break` is the standard way to break two levels; both
# loop-exit edges and the enclosing finally interact here.
try:
    for i in outer_items:
        for j in inner_items:
            if check(j):
                break
        else:
            continue
        break
finally:
    cleanup()

# --- 9. Functions: return crossing loops and finallys ------------------------
def drain(it):
    # `return` from inside `except` inside `while` inside `try/finally`.
    try:
        while True:
            try:
                h = next(it)
            except StopIteration:
                return 0
            probe(h)
    finally:
        cleanup()

def nested_return(outer, inner):
    # `return` crossing two finallys and two loop levels.
    for p in outer:
        try:
            for q in inner:
                try:
                    if check(q):
                        return q
                finally:
                    note(12)
        finally:
            cleanup()
    return 0

def loop_else_return(items):
    # `return` in a for/else, and a `break` that skips it.
    for r in items:
        if check(r):
            break
    else:
        return 1
    return 2

drain(iter(inner_items))
nested_return(outer_items, inner_items)
loop_else_return(outer_items)

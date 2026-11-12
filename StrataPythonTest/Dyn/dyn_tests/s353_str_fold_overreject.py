# A % whose left operand the translator may take for a str but that CPython's AST optimizer doesn't
# fold into one (a slice, a negative, boolean, computed or out-of-range index, a str operator that
# fails, a tuple with an item that fails) keeps its % in CPython, and raises at run time. The
# translator still rejects each one: its check takes any such subscript or operator for a str.
x = 3
for f in [lambda: ("a", 1)[0:1] % (x,), lambda: ("a", 1)[-1] % (x,), lambda: ("a", 1)[True] % (x,),
          lambda: ("a", 1)[1 - 0] % (x,), lambda: ("%s",)[5] % (x,), lambda: ("a" + 1) % (x,),
          lambda: (1 / 0, "%s")[1] % (x,)]:
    try:
        f()
    except Exception as e:
        print(type(e).__name__, e)

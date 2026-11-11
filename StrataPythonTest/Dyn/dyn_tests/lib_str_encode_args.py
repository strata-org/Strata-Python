# str.encode converts its arguments as Argument Clinic does: the encoding's type and NUL first,
# then the errors argument.
def show(f):
    try:
        print(repr(f()))
    except Exception as e:
        print(type(e).__name__, e)


show(lambda: "x".encode("utf-8\x00", 5))
show(lambda: "x".encode(5, 5))
show(lambda: "x".encode("utf-8", "x\x00"))
show(lambda: "x".encode("utf-8", 5))
show(lambda: "x".encode(errors="strict"))

# An error that a decoding meets after a handler gave a lone surrogate stops with a gap: CPython
# raises it with the args of the first error.
try:
    str(b"\x00\xd8\x41", "utf-16", "surrogatepass")
except UnicodeDecodeError as e:
    print(e.args[2:])

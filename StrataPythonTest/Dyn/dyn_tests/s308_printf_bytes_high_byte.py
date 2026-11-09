# Test: a bytes format with a byte of 0x80 or more right after width digits raises ValueError
f = b'%5\xff'
try:
    f % (1,)
except ValueError as e:
    print("ValueError", e)
except OverflowError as e:
    print("OverflowError", e)

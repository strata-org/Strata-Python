# Attribute write: boundary case. Dynamic attribute creation outside __init__
# breaks the field-array model.
"""Attribute write: boundary case.
Dynamic attribute creation outside __init__ breaks the field-array model.
"""

class Flexible:
    def __init__(self):
        self.x = 1

if __name__ == "__main__":
    obj = Flexible()
    print(obj.x)        # 1 -- model handles this

    obj.y = 99          # dynamic attribute creation -- no field array for 'y'
    print(obj.y)        # 99 -- model would fail (no Heap_Flexible_y exists)

    del obj.x           # attribute deletion -- field arrays can't model absence
    try:
        print(obj.x)
    except AttributeError as e:
        print(f"Error: {e}")  # model can't represent this state

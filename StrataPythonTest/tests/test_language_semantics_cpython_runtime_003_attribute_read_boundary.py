# Attribute read: boundary case. __getattr__ makes attribute access dynamic —
# the simplified model would miss the fallback and get the wrong result.
"""Attribute read: boundary case.
__getattr__ makes attribute access dynamic — the simplified model
would miss the fallback and get the wrong result.
"""

class DynamicAttrs:
    def __init__(self):
        self.real_attr = 42

    def __getattr__(self, name: str):
        # Called when normal lookup fails
        return f"dynamic:{name}"

if __name__ == "__main__":
    obj = DynamicAttrs()
    print(obj.real_attr)    # 42 -- model would get this right
    print(obj.fake_attr)    # dynamic:fake_attr -- model would raise AttributeError
    print(obj.anything)     # dynamic:anything -- model has no field for this

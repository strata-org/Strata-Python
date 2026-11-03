# Test: BaseExceptionGroup checks its items with isinstance, which reads their __class__
class K(KeyboardInterrupt):
    @property
    def __class__(self):
        print("class read")
        return ValueError
g = BaseExceptionGroup("m", [K()])
print(type(g).__name__)

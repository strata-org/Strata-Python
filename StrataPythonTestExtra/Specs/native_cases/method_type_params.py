# Type parameters on a method are not supported: the model is rejected.
class T:
    pass

class Box:
    def get[T](self, x: T) -> T:
        ...

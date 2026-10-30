# A stub's __init__ follows the rules of every method, so a default other than None
# rejects the model.
class C:
    def __init__(self, n: int = 0) -> None:
        ...

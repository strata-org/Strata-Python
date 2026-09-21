# The extern rebinding of T must keep its source position after the class.
class T:
    x: int


from extern_helper_mod import U as T

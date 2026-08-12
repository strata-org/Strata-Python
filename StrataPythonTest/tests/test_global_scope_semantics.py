counter: int = 1
tuple_left: int = 40
tuple_right: int = 50
import_shadow: int = 60


def read_counter() -> int:
    return counter


def increment_counter():
    global counter
    counter += 1


def create_global():
    if True:
        global created_in_function
    created_in_function = 7


def local_shadow() -> int:
    counter: int = 20
    counter += 2
    return counter


def parameter_shadow(counter: int) -> int:
    return counter + 1


def local_binding_forms() -> int:
    tuple_left, tuple_right = (1, 2)
    import sys as import_shadow
    tuple_left += 1
    return tuple_left + tuple_right


increment_counter()
increment_counter()
create_global()

assert read_counter() == 3, "function reads updated module field"
assert created_in_function == 7, "global declaration creates module field"
assert local_shadow() == 22, "local assignment shadows module field"
assert parameter_shadow(30) == 31, "parameter shadows module field"
assert local_binding_forms() == 4, "all function binding forms remain local"
assert counter == 3, "local and parameter shadows do not mutate module field"
assert tuple_left == 40, "destructuring does not mutate module field"
assert tuple_right == 50, "destructuring does not mutate second module field"
assert import_shadow == 60, "local import does not mutate module field"

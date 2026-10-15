# A yield the enclosing function evaluates makes it a generator, as in CPython 3.12, also
# where a nested scope begins: a nested def's annotations, and a comprehension's outermost
# iterable.
def positional_annotation():
    def h(x: (yield 1)):
        pass

def positional_only_annotation():
    def h(x: (yield 1), /):
        pass

def varargs_annotation():
    def h(*a: (yield 1)):
        pass

def keyword_only_annotation():
    def h(*, b: (yield 1)):
        pass

def kwargs_annotation():
    def h(**k: (yield 1)):
        pass

def return_annotation():
    def h() -> (yield 1):
        pass

def first_annotation():
    def h(p: (yield 1), /, a: (yield 2)):  # the diagnostic names the first in source order
        pass

def list_iterable(xs):
    return [x for x in (yield xs)]

def set_iterable(xs):
    return {x for x in (yield xs)}

def dict_iterable(xs):
    return {x: 1 for x in (yield xs)}

def generator_iterable(xs):
    return (x for x in (yield xs))

def class_decorator_first():
    @(yield 1)  # a class's decorators and bases are evaluated where the class is
    class C((yield 2)):
        pass

async def async_generator():
    yield 1  # an async generator: CPython's CO_ASYNC_GENERATOR

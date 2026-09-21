# A dotted import rebinds its top-level name: a scratch class of that name
# must not resolve for a later ghost type.
class import_test:
    k: str


import import_test.service.module

ghost(name="g", type=import_test)

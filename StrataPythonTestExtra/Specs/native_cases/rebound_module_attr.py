# A pin of a result that is wrong today: after m = 0, CPython has no m.ServiceClass, but
# PySpec still reads the attribute through the import.
import import_test.service.module as m
m = 0


def f(x: m.ServiceClass) -> None:
    ...

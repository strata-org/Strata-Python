# A from-import of a model module rebinds the earlier assignment, so the ghost sees the
# imported class.
MyType = int
from import_test.service.module import ServiceClass as MyType
ghost(name="g", type=MyType)

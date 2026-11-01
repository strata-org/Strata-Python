# Test: import of the builtins module, and from-imports of its names
import builtins
from builtins import len as length, print as p
p("imported")

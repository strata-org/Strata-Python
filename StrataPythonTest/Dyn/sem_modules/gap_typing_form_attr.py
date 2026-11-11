# A special form's __getattr__ raises AttributeError(name), whose name and obj the model leaves out.
from typing import Optional
print(Optional.__name__)
try:
    Optional.foo
except AttributeError as e:
    print("AttributeError:", e)

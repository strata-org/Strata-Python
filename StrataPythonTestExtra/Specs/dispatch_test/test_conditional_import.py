# The nested re-import must not be mistaken for an assignment that would
# suppress the top-level import's binding.
from servicelib.Contract import modeled_text

try:
    from servicelib.Contract import modeled_text
except:
    pass


def check_conditional_import() -> bool:
    value = modeled_text("key")
    return value is not None

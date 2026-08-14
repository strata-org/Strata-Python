# Nested OLD is preserved structurally. Laurel diagnoses and normalizes the
# redundant inner wrapper.
@admit(lambda x, result: OLD(OLD(x)) >= x)
def f(x: int) -> int:
    ...

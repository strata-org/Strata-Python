# A model with a declared parameter type and no contract at all. The declared
# type is the only obligation it carries, so a caller passing the wrong type is
# caught by that and nothing else.
def needs_int(n: int) -> int:
    ...

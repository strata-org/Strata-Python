# INVALID Python: `connect` is never imported, so this raises NameError at
# runtime; resolution must not treat the bare name as a dispatch factory.
def user_call():
    return connect("storage")

# `connect` comes from an UNRELATED (unmodeled) module: it must not pick up
# the servicelib dispatch table just because the names match.
from unrelated_library import connect


def user_call():
    return connect("storage")

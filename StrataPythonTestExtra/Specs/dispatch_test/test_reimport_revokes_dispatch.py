# The second import shadows the dispatch-module `connect`; the bare call must
# NOT dispatch through the stale servicelib origin.
from servicelib import connect
from unrelated_library import connect


def user_call():
    return connect("storage")

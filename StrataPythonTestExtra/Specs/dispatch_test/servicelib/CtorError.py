# A model exception whose constructor has a contract. The Laurel front ends do not
# check it at any call yet (card "Laurel front ends: Check model constructor
# contracts").
class ClientError(Exception):
    @requires(lambda operation: len(operation) >= 3)
    def __init__(self, response: str, operation: str) -> None:
        ...

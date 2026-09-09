class EqOnly:
    def __eq__(self, other):
        return True


class HashOnly:
    def __hash__(self):
        return 7

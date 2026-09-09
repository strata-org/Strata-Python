class Proxy:
    def __getattr__(self, name):
        return 0

    def __setattr__(self, name, value):
        pass

    def __new__(cls):
        return object.__new__(cls)

    def __init_subclass__(cls):
        pass

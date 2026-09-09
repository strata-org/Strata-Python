# A program that works BECAUSE class scope is opaque to methods
class Config:
    default = 10
    def get(self):
        return self.default  # must use self, not bare 'default'
c = Config()
c.default = 42
assert c.get() == 42  # instance attribute wins
print("OK: class scope opacity — self.x required, not bare x")

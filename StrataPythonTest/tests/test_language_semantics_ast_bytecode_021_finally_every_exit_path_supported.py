# finally always runs — resource cleanup pattern
class Resource:
    def __init__(self): self.open = True
    def close(self): self.open = False
def use_resource():
    r = Resource()
    try:
        return r
    finally:
        r.close()
r = use_resource()
assert r.open == False  # finally ran even with return
print("OK: finally — cleanup runs on every exit path")

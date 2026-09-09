# Class body executes at definition time
registry = []
class Plugin:
    registry.append("Plugin")
    name = "plugin"
assert registry == ["Plugin"]
assert Plugin.name == "plugin"
print("OK: class body — executes immediately, populates namespace")

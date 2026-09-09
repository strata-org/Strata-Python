# or returns first truthy value, not True
default_config = {"debug": False}
config = None
active = config or default_config  # returns the dict, not True
assert active is default_config
print("OK: boolean short-circuit — returns operand value")

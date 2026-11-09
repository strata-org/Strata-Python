# Test: a dict iterator's length hint, which the model doesn't hold yet
print(len([*iter({1: 2})]))

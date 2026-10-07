# Test: `**` unpacking in a dict display lowers to dictUpdate (last wins),
# distinct from a call site's dictMerge (duplicate key is an error).
a = {"x": 1}
b = {"y": 2}

only_literal = {"k": 1, "j": 2}
only_star = {**a}
star_then_literal = {**a, "z": 3}
literal_then_star = {"z": 3, **a}
two_stars = {**a, **b}
mixed = {"p": 0, **a, "q": 1, **b, "r": 2}
empty = {}

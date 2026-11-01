# Test: two ** arguments with the same key raise TypeError naming the callee
print(**{"sep": "-"}, **{"sep": "+"})

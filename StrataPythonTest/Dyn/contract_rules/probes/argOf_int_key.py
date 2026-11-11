args = ()
kwargs = {1: "one", True: "t"}
d = 7
# probe: py.Value = py.argOf($args, $kwargs, -1, "1", $d)
# python: contract_rules_ref.argOf_ref(args, kwargs, -1, "1", d)
# expect: agree

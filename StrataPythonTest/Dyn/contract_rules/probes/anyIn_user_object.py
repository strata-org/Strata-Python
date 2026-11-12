class Foo:
    pass
xs = Foo()
def pred(x):
    return x
# probe: base.Bool = py.anyIn($xs) ^err {pred}
# python: contract_rules_ref.anyIn_ref(xs, pred)
# expect: agree

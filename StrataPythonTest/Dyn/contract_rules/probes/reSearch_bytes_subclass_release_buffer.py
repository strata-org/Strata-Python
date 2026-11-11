log = []
class B(bytes):
    def __release_buffer__(self, view):
        log.append("released")
s = B(b"ab")
# probe: base.Bool = py.reSearch("a", $s) ^err
# python: contract_rules_ref.reSearch_ref('a', s)
# expect: gap py.reSearch: a subject whose class defines __release_buffer__ is not modelled

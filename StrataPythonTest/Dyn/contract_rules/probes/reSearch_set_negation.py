s = "abc]"
# probe: base.Bool = py.reSearch("[^a-c]", $s) ^err
# python: contract_rules_ref.reSearch_ref('[^a-c]', s)
# expect: agree

# Test: a str literal with a lone surrogate (a known bug: the literal reaches the translator
# as its escape text, so the comparison is True)
x = "\udc80" == "\\udc80"

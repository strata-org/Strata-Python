word = "helloworld"

assert word[0:10] == "helloworld"

assert word[1:4] == "ell"

assert word[:5] == "hello"

assert word[5:] == "world"

assert word[-5:] == "world"

assert word[-100:100] == "helloworld"

assert word[4:2] == ""

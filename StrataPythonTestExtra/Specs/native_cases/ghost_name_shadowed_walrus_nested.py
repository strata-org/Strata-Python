# A walrus nested inside a call still binds `ghost` at module scope.
print(ghost := 5)
ghost(name="nested_walrus_collide", type=int, init=0)

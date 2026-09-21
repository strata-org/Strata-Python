# A walrus binding shadowing `ghost` makes later calls ordinary expressions.
(ghost := 5)
ghost(name="walrus_collide", type=int, init=0)

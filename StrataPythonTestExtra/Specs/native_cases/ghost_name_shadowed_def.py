# A function definition shadowing `ghost` makes later calls ordinary expressions.
def ghost(name: str) -> None:
    ...


ghost(name="collide")

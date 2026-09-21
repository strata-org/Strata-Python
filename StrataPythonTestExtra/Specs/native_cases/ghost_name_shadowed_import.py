# An import alias shadowing `ghost` makes later calls ordinary expressions.
import typing as ghost

ghost(name="collide", type=int, init=0)

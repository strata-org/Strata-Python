# isinstance narrowing killed by unrelated method call — conservative
# assumption invalidation after ANY call destroys narrowing on untouched
# variables
"""
ISINSTANCE NARROWING LOST AFTER FUNCTION CALL ON UNRELATED OBJECT

The subset allows:
  - isinstance narrowing (IN)
  - Method calls (IN)
  - Multiple objects in scope (IN)

The NOVEL gap: after isinstance narrowing establishes a type for variable
`x`, a method call on a DIFFERENT object `y.method()` may invalidate
the narrowing of `x` in the model, even though CPython's `x` is unchanged.

  class Animal: ...
  class Dog(Animal):
      breed: str

  def process(animals: list[Animal], logger: Logger) -> str:
      a: Animal = animals[0]
      if isinstance(a, Dog):
          # Here: a is narrowed to Dog, a.breed is accessible
          logger.log("found dog")  # unrelated method call
          # Model may HAVOC all assumptions after method call
          # including the isinstance narrowing on `a`
          return a.breed  # Model: narrowing lost → Hole or TypeError
      return "not a dog"

In CPython, calling `logger.log()` cannot change the type of `a`.
But in the model, if method calls havoc the heap (finding 103/196)
or invalidate all assumptions (conservative approach), the narrowing
`assume(classname(a) == "Dog")` may be killed.

This is distinct from:
  - Finding 162 (narrowing invalidated by REASSIGNMENT) — that's about
    reassigning the narrowed variable itself
  - Finding 334 (narrowing killed at branch merge) — that's about
    control flow merging
  - Finding 441 (repeated field access narrowing lost) — that's about
    re-reading the same field
  - Finding 103/196 (no modifies clause) — those are the ROOT CAUSE,
    but this finding shows the SPECIFIC consequence for isinstance

The key insight: isinstance narrowing is an ASSUMPTION about a variable's
tag. If the model conservatively invalidates all assumptions after any
method call (because it can't prove the call doesn't affect the variable),
then narrowing becomes useless in any function that does work between
the isinstance check and the field access.
"""
from dataclasses import dataclass


@dataclass
class Shape:
    name: str


@dataclass
class Circle(Shape):
    radius: int


@dataclass
class Rectangle(Shape):
    width: int
    height: int


@dataclass
class Logger:
    count: int

    def log(self: "Logger", msg: str) -> "Logger":
        """Pure logging — returns new Logger with incremented count."""
        return Logger(count=self.count + 1)


def area_with_logging(shape: Shape, logger: Logger) -> int:
    """Compute area after isinstance check, with unrelated call between.
    
    CPython: isinstance narrows shape, logger.log() doesn't affect shape,
             field access on shape works fine.
    Model: logger.log() may havoc assumptions → narrowing on shape lost →
           shape.radius/width/height access fails.
    """
    if isinstance(shape, Circle):
        # Narrowing: shape is Circle, has .radius
        logger = logger.log("computing circle area")
        # After this call, is shape still narrowed to Circle?
        # CPython: YES (logger.log can't change shape's type)
        # Model: MAYBE NOT (if call havocs all assumptions)
        r: int = shape.radius
        return r * r * 3  # approximate pi*r^2
    if isinstance(shape, Rectangle):
        logger = logger.log("computing rectangle area")
        # Same issue: is shape still narrowed to Rectangle?
        w: int = shape.width
        h: int = shape.height
        return w * h
    return 0


def classify_with_work(shapes: list[Shape]) -> list[int]:
    """Process shapes with isinstance, doing work between check and access.
    
    The "work" is operations on OTHER variables that should not
    invalidate the isinstance narrowing.
    """
    areas: list[int] = []
    total: int = 0
    for s in shapes:
        if isinstance(s, Circle):
            # Do some unrelated computation
            total = total + 1
            # Now access the narrowed field
            areas.append(s.radius * s.radius * 3)
        elif isinstance(s, Rectangle):
            total = total + 1
            areas.append(s.width * s.height)
    return areas


def narrowing_survives_local_computation(s: Shape) -> int:
    """isinstance check, then local arithmetic, then field access.
    
    Even pure local computation (no method calls) might cause the
    model to "forget" the narrowing if it's implemented as a
    single-use assumption rather than a persistent constraint.
    """
    if isinstance(s, Circle):
        # Local computation that doesn't touch s
        x: int = 2 + 3
        y: int = x * x
        # Is s still narrowed to Circle here?
        return s.radius + y
    return 0


def narrowing_across_conditional(s: Shape, flag: bool) -> int:
    """isinstance check, then conditional on unrelated variable, then access.
    
    The conditional branch on `flag` should not affect narrowing of `s`.
    """
    if isinstance(s, Rectangle):
        bonus: int = 0
        if flag:
            bonus = 10
        # After the if/else on flag, is s still narrowed?
        # CPython: yes
        # Model: if branch merge kills all assumptions → narrowing lost
        return s.width * s.height + bonus
    return 0


def main() -> None:
    logger: Logger = Logger(count=0)

    # Circle area with logging between check and access
    c: Shape = Circle(name="c1", radius=5)
    assert area_with_logging(c, logger) == 75  # 5*5*3

    # Rectangle area with logging between check and access
    r: Shape = Rectangle(name="r1", width=4, height=6)
    assert area_with_logging(r, logger) == 24  # 4*6

    # Multiple shapes
    shapes: list[Shape] = [
        Circle(name="a", radius=3),
        Rectangle(name="b", width=2, height=5),
        Circle(name="c", radius=1),
    ]
    areas: list[int] = classify_with_work(shapes)
    assert areas[0] == 27  # 3*3*3
    assert areas[1] == 10  # 2*5
    assert areas[2] == 3   # 1*1*3

    # Narrowing survives local computation
    assert narrowing_survives_local_computation(Circle(name="x", radius=4)) == 29  # 4 + 25

    # Narrowing survives unrelated conditional
    assert narrowing_across_conditional(Rectangle(name="y", width=3, height=7), True) == 31  # 21 + 10
    assert narrowing_across_conditional(Rectangle(name="y", width=3, height=7), False) == 21  # 21 + 0

    print("all passed")


main()

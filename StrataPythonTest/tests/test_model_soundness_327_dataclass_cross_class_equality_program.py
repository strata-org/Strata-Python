# @dataclass cross-class equality — `Point(1,2) == Vector(1,2)` must be False;
# PEq must check classname before attrs
"""
@dataclass cross-class equality — different classes are never equal.

In CPython, @dataclass-generated __eq__ checks type FIRST:
  Point(1, 2) == Point(1, 2)       → True  (same class, same fields)
  Point(1, 2) == ColorPoint(1, 2)  → False (different class!)

Even if all fields match, objects of different @dataclass types are
NOT equal. The generated __eq__ does:
  def __eq__(self, other):
      if other.__class__ is self.__class__:
          return (self.x, self.y) == (other.x, other.y)
      return NotImplemented

The Laurel model's PEq on from_ClassInstance uses structural equality
on the DictStrAny (instance_attributes). If two different classes happen
to have the same field names and values, the model might say they're
equal — but CPython says they're NOT.

Finding 037 covers non-@dataclass equality (identity vs structural).
Finding 213 confirms @dataclass structural eq is correct for SAME class.
This finding tests CROSS-CLASS comparison where classname differs.

Uses ONLY confirmed-accepted constructs: @dataclass, ==, !=.
"""
from dataclasses import dataclass


@dataclass
class Point2D:
    x: int
    y: int


@dataclass
class Vector2D:
    x: int
    y: int


@dataclass
class Pixel:
    x: int
    y: int


def same_class_equal() -> bool:
    """Same class, same fields → equal."""
    return Point2D(1, 2) == Point2D(1, 2)
    # CPython: True
    # Model: structural eq on attrs → True (correct)


def different_class_same_fields() -> bool:
    """Different class, same field names and values → NOT equal."""
    return Point2D(1, 2) == Vector2D(1, 2)  # type: ignore
    # CPython: False (different __class__)
    # Model: if PEq only compares attrs dict, both have {"x":1,"y":2}
    #   → True — WRONG


def different_class_not_equal() -> bool:
    """Confirm inequality."""
    return Point2D(1, 2) != Vector2D(1, 2)  # type: ignore
    # CPython: True (they are NOT equal)
    # Model: may say False (thinks they ARE equal)


def three_classes_all_different() -> bool:
    """Three classes with identical fields — all pairwise unequal."""
    p: Point2D = Point2D(5, 10)
    v: Vector2D = Vector2D(5, 10)
    px: Pixel = Pixel(5, 10)
    r1: bool = p != v  # type: ignore
    r2: bool = p != px  # type: ignore
    r3: bool = v != px  # type: ignore
    return r1 and r2 and r3
    # CPython: True (all different classes)
    # Model: may say False


def main() -> None:
    assert same_class_equal() == True
    assert different_class_same_fields() == False
    assert different_class_not_equal() == True
    assert three_classes_all_different() == True

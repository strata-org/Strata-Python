# Method call on narrowed Optional field — three-way failure: field access
# untyped + narrowing incomplete (no classname) + dispatch needs classname;
# Hole
"""
METHOD CALL ON NARROWED OPTIONAL FIELD — DISPATCH FAILS AFTER NARROWING

The subset allows:
  - @dataclass with Optional[UserClass] fields (IN)
  - `is not None` narrowing (IN)
  - Method calls on narrowed variables (IN)
  - Field access on narrowed variables (IN)

The NOVEL gap: after narrowing an Optional[UserClass] field via
`if obj.field is not None`, the narrowed value should support method
calls. But the model has TWO compounding problems:

  1. Field access returns untyped Any (finding 441: repeated field access)
  2. Method dispatch requires classname (finding 375: dispatch uses classname)

Combined, the narrowed field value has:
  - Tag: known to be from_ClassInstance (narrowing killed from_None)
  - Classname: UNKNOWN (DictStrAny_get returns opaque Any)
  - Method dispatch: FAILS (no classname to select method)

  @dataclass
  class Engine:
      horsepower: int
      
      def is_powerful(self) -> bool:
          return self.horsepower > 200

  @dataclass
  class Car:
      name: str
      engine: Optional[Engine]

  def check_power(car: Car) -> bool:
      if car.engine is not None:
          # Narrowed: car.engine is Engine (not None)
          # CPython: calls Engine.is_powerful() → True/False
          # Model: car.engine is from_ClassInstance(???, ???)
          #   classname unknown → method dispatch fails → Hole
          return car.engine.is_powerful()
      return False

ROOT CAUSE CHAIN:
  1. `car.engine` → DictStrAny_get(car.attrs, "engine") → opaque Any
  2. Narrowing: assume(!isfrom_None(car.engine)) → know it's ClassInstance
  3. But classname is STILL unknown: isfrom_ClassInstance(x) doesn't tell
     us WHICH class it is
  4. Method dispatch: Engine_is_powerful(x) requires
     assert(ClassInstance_classname(x) == "Engine") → UNPROVABLE
  5. Result: Hole or verification failure

This is distinct from:
  - Finding 441 (repeated field access narrowing lost) — that's about
    the SAME field read twice; this is about METHOD CALL after narrowing
  - Finding 235 (isinstance narrows but field access fails) — that's
    about isinstance, not Optional narrowing via `is not None`
  - Finding 062 (is None narrowing Optional) — that's about the
    narrowing mechanism itself, not the downstream method dispatch
  - Finding 375 (classname-based dispatch) — that's the general
    dispatch problem; this is the specific interaction with Optional

The interaction of Optional narrowing + field access + method dispatch
creates a THREE-WAY failure that none of the individual findings cover.
"""
from dataclasses import dataclass
from typing import Optional


@dataclass
class Engine:
    horsepower: int
    fuel_type: str

    def is_powerful(self: "Engine") -> bool:
        return self.horsepower > 200

    def efficiency_rating(self: "Engine") -> int:
        if self.fuel_type == "electric":
            return 95
        if self.fuel_type == "hybrid":
            return 70
        return 40


@dataclass
class Warranty:
    years: int
    miles: int

    def is_expired(self: "Warranty", current_miles: int) -> bool:
        return current_miles > self.miles

    def remaining_miles(self: "Warranty", current_miles: int) -> int:
        if current_miles >= self.miles:
            return 0
        return self.miles - current_miles


@dataclass
class Car:
    name: str
    engine: Optional[Engine]
    warranty: Optional[Warranty]
    mileage: int


def check_power(car: Car) -> bool:
    """Call method on narrowed Optional field.
    
    CPython: if engine exists, calls is_powerful() → bool
    Model: field access returns opaque Any; after narrowing,
           classname unknown; method dispatch fails
    """
    if car.engine is not None:
        return car.engine.is_powerful()
    return False


def get_efficiency(car: Car) -> int:
    """Chain: narrow Optional, then call method on narrowed value.
    
    Same three-way failure: narrow + field access + dispatch.
    """
    if car.engine is not None:
        return car.engine.efficiency_rating()
    return 0


def check_warranty_status(car: Car) -> str:
    """Multiple Optional fields, each narrowed independently.
    
    Model must handle narrowing of DIFFERENT Optional fields
    without conflating them.
    """
    if car.warranty is not None:
        if car.warranty.is_expired(car.mileage):
            return "expired"
        remaining: int = car.warranty.remaining_miles(car.mileage)
        if remaining < 10000:
            return "expiring_soon"
        return "active"
    return "no_warranty"


def combined_check(car: Car) -> str:
    """Both Optional fields narrowed in same function.
    
    Model must maintain SEPARATE narrowing for engine and warranty.
    """
    if car.engine is not None and car.warranty is not None:
        if car.engine.is_powerful() and not car.warranty.is_expired(car.mileage):
            return "powerful_and_covered"
    if car.engine is not None:
        if car.engine.is_powerful():
            return "powerful_no_warranty"
    return "basic"


def field_access_then_method(car: Car) -> int:
    """Access field of narrowed Optional, then call method.
    
    Two-step: narrow engine, read engine.horsepower, call method.
    Each step requires the narrowing to persist.
    """
    if car.engine is not None:
        hp: int = car.engine.horsepower
        is_strong: bool = car.engine.is_powerful()
        if is_strong:
            return hp
        return 0
    return -1


def main() -> None:
    powerful_car: Car = Car(
        name="Sports",
        engine=Engine(horsepower=300, fuel_type="gas"),
        warranty=Warranty(years=5, miles=60000),
        mileage=20000
    )
    weak_car: Car = Car(
        name="Economy",
        engine=Engine(horsepower=100, fuel_type="hybrid"),
        warranty=None,
        mileage=50000
    )
    no_engine: Car = Car(
        name="Shell",
        engine=None,
        warranty=None,
        mileage=0
    )

    # check_power
    assert check_power(powerful_car) == True
    assert check_power(weak_car) == False
    assert check_power(no_engine) == False

    # get_efficiency
    assert get_efficiency(powerful_car) == 40
    assert get_efficiency(weak_car) == 70
    assert get_efficiency(no_engine) == 0

    # check_warranty_status
    assert check_warranty_status(powerful_car) == "active"
    assert check_warranty_status(weak_car) == "no_warranty"

    # combined_check
    assert combined_check(powerful_car) == "powerful_and_covered"
    assert combined_check(weak_car) == "basic"

    # field_access_then_method
    assert field_access_then_method(powerful_car) == 300
    assert field_access_then_method(weak_car) == 0
    assert field_access_then_method(no_engine) == -1

    print("all passed")


main()

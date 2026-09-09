"""The first MRO entry masks a deeper property before descriptor precedence."""


class Base:
    @property
    def value(self):
        return "base-property"


class Child(Base):
    value = "child-class-value"


without_field = Child()
with_field = Child()
with_field.value = "instance-value"

RESULT = (without_field.value, with_field.value)

# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
class Gauge:
    _reading: int

    # L4 pyhard[summary Gauge.__init__] returns={NoneType}; escapes={}
    # L4 pyhard[type parameter] assert/assume conforms(reading, int); boundary nondet over 19 closed tags
    def __init__(self, reading: int):
        # L5 pyhard[flow Gauge.__init__ in] reading -> (binding=definitely_bound; tags={bool, int}; defs={param:reading}), self -> (binding=definitely_bound; tags={Gauge}; defs={param:self}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external})
        # L5 pyhard[flow Gauge.__init__ out] reading -> (binding=definitely_bound; tags={bool, int}; defs={param:reading}), self -> (binding=definitely_bound; tags={Gauge}; defs={param:self}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external})
        # L5 pyhard[read Gauge.__init__.reading@25] binding=definitely_bound
        # L5 pyhard[read Gauge.__init__.self@9] binding=definitely_bound
        # L5 pyhard[type field_write] assert/assume conforms(Gauge._reading, int); observed={bool, int}
        # L5 pyhard[dispatch self._reading] assert/assume key in {Gauge}
        # L5 pyhard[row {Gauge}] store_declared_field; owner=Gauge; result={NoneType}
        self._reading = reading

    @property
    # L8 pyhard[summary Gauge.reading] returns={bool, int}; escapes={}
    def reading(self) -> int:
        # L9 pyhard[flow Gauge.reading in] self -> (binding=definitely_bound; tags={Gauge}; defs={param:self}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external})
        # L9 pyhard[flow Gauge.reading out:return] $result -> (binding=definitely_bound; tags={bool, int}; defs={return}), self -> (binding=definitely_bound; tags={Gauge}; defs={param:self}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external})
        # L9 pyhard[read Gauge.reading.self@16] binding=definitely_bound
        # L9 pyhard[type return] assert/assume conforms(result, int); observed={bool, int}
        # L9 pyhard[dispatch self._reading] assert/assume key in {Gauge}
        # L9 pyhard[row {Gauge}] read_declared_field; owner=Gauge; result={bool, int}
        return self._reading

    @reading.setter
    # L12 pyhard[summary Gauge.reading$setter] returns={NoneType}; escapes={}
    # L12 pyhard[type implicit_return] assert/assume conforms(result, NoneType); observed={NoneType}
    # L12 pyhard[type parameter] assert/assume conforms(value, int); boundary nondet over 19 closed tags
    def reading(self, value: int) -> None:
        # L13 pyhard[flow Gauge.reading$setter in] self -> (binding=definitely_bound; tags={Gauge}; defs={param:self}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}), value -> (binding=definitely_bound; tags={bool, int}; defs={param:value})
        # L13 pyhard[flow Gauge.reading$setter out] self -> (binding=definitely_bound; tags={Gauge}; defs={param:self}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}), value -> (binding=definitely_bound; tags={bool, int}; defs={param:value})
        # L13 pyhard[read Gauge.reading.value@25] binding=definitely_bound
        # L13 pyhard[read Gauge.reading.self@9] binding=definitely_bound
        # L13 pyhard[type field_write] assert/assume conforms(Gauge._reading, int); observed={bool, int}
        # L13 pyhard[dispatch self._reading] assert/assume key in {Gauge}
        # L13 pyhard[row {Gauge}] store_declared_field; owner=Gauge; result={NoneType}
        self._reading = value


class Panel:
    gauge: Gauge

    # L19 pyhard[summary Panel.__init__] returns={NoneType}; escapes={}
    # L19 pyhard[type parameter] assert/assume conforms(gauge, Gauge); boundary nondet over 19 closed tags
    def __init__(self, gauge: Gauge):
        # L20 pyhard[flow Panel.__init__ in] gauge -> (binding=definitely_bound; tags={Gauge}; defs={param:gauge}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}), self -> (binding=definitely_bound; tags={Panel}; defs={param:self}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}); aliases may={gauge~self} must={}
        # L20 pyhard[flow Panel.__init__ out] gauge -> (binding=definitely_bound; tags={Gauge}; defs={param:gauge}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}), self -> (binding=definitely_bound; tags={Panel}; defs={param:self}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}); aliases may={gauge~self} must={}
        # L20 pyhard[read Panel.__init__.gauge@22] binding=definitely_bound
        # L20 pyhard[read Panel.__init__.self@9] binding=definitely_bound
        # L20 pyhard[type field_write] assert/assume conforms(Panel.gauge, Gauge); observed={Gauge}
        # L20 pyhard[dispatch self.gauge] assert/assume key in {Panel}
        # L20 pyhard[row {Panel}] store_declared_field; owner=Panel; result={NoneType}
        self.gauge = gauge


class Console:
    panel: Panel

    # L26 pyhard[summary Console.__init__] returns={NoneType}; escapes={}
    # L26 pyhard[type parameter] assert/assume conforms(panel, Panel); boundary nondet over 19 closed tags
    def __init__(self, panel: Panel):
        # L27 pyhard[flow Console.__init__ in] panel -> (binding=definitely_bound; tags={Panel}; defs={param:panel}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}), self -> (binding=definitely_bound; tags={Console}; defs={param:self}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}); aliases may={panel~self} must={}
        # L27 pyhard[flow Console.__init__ out] panel -> (binding=definitely_bound; tags={Panel}; defs={param:panel}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}), self -> (binding=definitely_bound; tags={Console}; defs={param:self}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}); aliases may={panel~self} must={}
        # L27 pyhard[read Console.__init__.panel@22] binding=definitely_bound
        # L27 pyhard[read Console.__init__.self@9] binding=definitely_bound
        # L27 pyhard[type field_write] assert/assume conforms(Console.panel, Panel); observed={Panel}
        # L27 pyhard[dispatch self.panel] assert/assume key in {Console}
        # L27 pyhard[row {Console}] store_declared_field; owner=Console; result={NoneType}
        self.panel = panel


# L30 pyhard[summary adjust] returns={bool, int}; escapes={}
# L30 pyhard[type parameter] assert/assume conforms(console, Console); boundary nondet over 19 closed tags
# L30 pyhard[type parameter] assert/assume conforms(value, int); boundary nondet over 19 closed tags
def adjust(console: Console, value: int) -> int:
    # L31 pyhard[flow adjust in] console -> (binding=definitely_bound; tags={Console}; defs={param:console}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}), value -> (binding=definitely_bound; tags={bool, int}; defs={param:value})
    # L31 pyhard[flow adjust out] console -> (binding=definitely_bound; tags={Console}; defs={param:console}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}), value -> (binding=definitely_bound; tags={bool, int}; defs={param:value})
    # L31 pyhard[read adjust.value@35] binding=definitely_bound
    # L31 pyhard[read adjust.console@5] binding=definitely_bound
    # L31 pyhard[type property_setter_argument] assert/assume conforms(value, int); observed={bool, int}
    # L31 pyhard[dispatch console.panel] assert/assume key in {Console}
    # L31 pyhard[row {Console}] read_declared_field; owner=Console; result={Panel}
    # L31 pyhard[dispatch console.panel.gauge] assert/assume key in {Panel}
    # L31 pyhard[row {Panel}] read_declared_field; owner=Panel; result={Gauge}
    # L31 pyhard[dispatch console.panel.gauge.reading] assert/assume key in {Gauge}
    # L31 pyhard[row {Gauge}] invoke_property_setter; owner=Gauge; label=Gauge.reading$setter; result={NoneType}
    console.panel.gauge.reading = value
    # L32 pyhard[flow adjust in] console -> (binding=definitely_bound; tags={Console}; defs={param:console}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}), value -> (binding=definitely_bound; tags={bool, int}; defs={param:value})
    # L32 pyhard[flow adjust out:return] $result -> (binding=definitely_bound; tags={bool, int}; defs={return}), console -> (binding=definitely_bound; tags={Console}; defs={param:console}; points-to={boundary:Console.__init__, boundary:Gauge.__init__, boundary:Gauge.reading, boundary:Gauge.reading$setter, boundary:Panel.__init__, boundary:adjust, boundary:external}), value -> (binding=definitely_bound; tags={bool, int}; defs={param:value})
    # L32 pyhard[read adjust.console@12] binding=definitely_bound
    # L32 pyhard[type return] assert/assume conforms(result, int); observed={bool, int}
    # L32 pyhard[dispatch console.panel] assert/assume key in {Console}
    # L32 pyhard[row {Console}] read_declared_field; owner=Console; result={Panel}
    # L32 pyhard[dispatch console.panel.gauge] assert/assume key in {Panel}
    # L32 pyhard[row {Panel}] read_declared_field; owner=Panel; result={Gauge}
    # L32 pyhard[dispatch console.panel.gauge.reading] assert/assume key in {Gauge}
    # L32 pyhard[row {Gauge}] invoke_property_getter; owner=Gauge; label=Gauge.reading; result={bool, int}
    return console.panel.gauge.reading

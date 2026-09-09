class Gauge:
    _reading: int

    def __init__(self, reading: int):
        self._reading = reading

    @property
    def reading(self) -> int:
        return self._reading

    @reading.setter
    def reading(self, value: int) -> None:
        self._reading = value


class Panel:
    gauge: Gauge

    def __init__(self, gauge: Gauge):
        self.gauge = gauge


class Console:
    panel: Panel

    def __init__(self, panel: Panel):
        self.panel = panel


def adjust(console: Console, value: int) -> int:
    console.panel.gauge.reading = value
    return console.panel.gauge.reading

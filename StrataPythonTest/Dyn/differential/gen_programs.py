"""Generate random Python programs that call the built-in library, for the differential runner.

    python3 gen_programs.py OUTDIR [--seed S] [--count N]

It writes `OUTDIR/gen_<S>_<i>.py` for i < N and prints their ids, one per line. The same seed
gives the same programs. Each program is deterministic, ends, and prints at every block entry. It
uses a few user classes (with `__eq__`, `__lt__`, `__gt__`, `__hash__`, `__add__`, `__radd__`
and `NotImplemented`, `__iter__`, `__len__`, `__length_hint__` and `__index__`), passes them and
built-in values to the library's functions and methods (user iterables as pairs too), with argument errors among them (an index
out of range, a missing key, a wrong type, a wrong number of arguments), changes containers while
it iterates over them, and catches what is raised. The output avoids what CPython's hash seed
and addresses change: its sets hold only ints or user objects with an int hash, it prints sets of
strings only through `sorted`, and it never prints the hash of a string or a bound method.
"""

import argparse
import pathlib
import random

CLASSES = {
    "N": '''class N:
    def __init__(self, v):
        self.v = v
    def __eq__(self, other):
        events.append("N.__eq__")
        return isinstance(other, N) and self.v == other.v
    def __lt__(self, other):
        events.append("N.__lt__")
        if not isinstance(other, N):
            return NotImplemented
        return self.v < other.v
    def __gt__(self, other):
        events.append("N.__gt__")
        if not isinstance(other, N):
            return NotImplemented
        return self.v > other.v
    def __hash__(self):
        return self.v
    def __repr__(self):
        return f"N({self.v})"
''',
    "Add": '''class Add:
    def __init__(self, v):
        self.v = v
    def __add__(self, other):
        events.append("Add.__add__")
        if isinstance(other, int):
            return Add(self.v + other)
        return NotImplemented
    def __radd__(self, other):
        events.append("Add.__radd__")
        if isinstance(other, int):
            return Add(other + self.v)
        return NotImplemented
    def __repr__(self):
        return f"Add({self.v})"
''',
    "It": '''class It:
    def __init__(self, items):
        self.items = list(items)
        self.i = 0
    def __iter__(self):
        events.append("It.__iter__")
        return self
    def __next__(self):
        if self.i >= len(self.items):
            events.append("It.stop")
            raise StopIteration
        self.i += 1
        return self.items[self.i - 1]
''',
    "Sized": '''class Sized:
    def __init__(self, n):
        self.n = n
    def __len__(self):
        events.append("Sized.__len__")
        return self.n
    def __iter__(self):
        return iter(range(self.n))
''',
    "Hint": '''class Hint:
    def __init__(self, n):
        self.n = n
    def __length_hint__(self):
        events.append("Hint.__length_hint__")
        return self.n
    def __iter__(self):
        return iter(range(self.n))
''',
    "Idx": '''class Idx:
    def __init__(self, v):
        self.v = v
    def __index__(self):
        events.append("Idx.__index__")
        return self.v
''',
}


class Gen:
    def __init__(self, rng):
        self.r = rng
        self.lines = []
        self.depth = 0
        self.vars = []
        self.n = 0

    def emit(self, line):
        self.lines.append("    " * self.depth + line)

    def fresh(self):
        self.n += 1
        return f"v{self.n}"

    # Values.
    def small_int(self):
        return str(self.r.choice([-3, -1, 0, 1, 2, 3, 5, 7, 10, 100]))

    def word(self):
        return repr(self.r.choice(["", "a", "ab", "Hello World", "  x y  ", "a,b,,c", "ΑΣ",
                                   "straße", "12", "١٢", "tab\there", "line1\nline2", "x_1"]))

    def int_list(self):
        n = self.r.randrange(0, 6)
        return "[" + ", ".join(self.small_int() for _ in range(n)) + "]"

    def str_list(self):
        n = self.r.randrange(0, 5)
        return "[" + ", ".join(self.word() for _ in range(n)) + "]"

    def n_list(self):
        n = self.r.randrange(0, 5)
        return "[" + ", ".join(f"N({self.small_int()})" for _ in range(n)) + "]"

    def int_iterable(self):
        """An iterable of ints only, for sets: a set of ints prints the same under every hash
        seed."""
        c = self.r.randrange(6)
        if c == 0:
            return self.int_list()
        if c == 1:
            return f"It({self.int_list()})"
        if c == 2:
            return f"range({self.small_int()})"
        if c == 3:
            return f"tuple({self.int_list()})"
        if c == 4:
            return f"Hint({self.r.randrange(0, 5)})"
        return "{" + ", ".join(f"{self.small_int()}: {self.word()}"
                               for _ in range(self.r.randrange(0, 4))) + "}"

    def iterable(self):
        c = self.r.randrange(7)
        if c == 0:
            return self.int_list()
        if c == 1:
            return f"It({self.int_list()})"
        if c == 2:
            return f"range({self.small_int()})"
        if c == 3:
            return f"tuple({self.int_list()})"
        if c == 4:
            return self.word()
        if c == 5:
            return f"Sized({self.r.randrange(0, 5)})"
        return "{" + ", ".join(f"{self.small_int()}: {self.word()}"
                               for _ in range(self.r.randrange(0, 4))) + "}"

    # Expressions that call the library.
    def call(self):
        r = self.r
        c = r.randrange(40)
        it = self.iterable()
        if c == 0:
            return f"sum({it})"
        if c == 1:
            return f"sum({self.int_list()}, {r.choice(['0', '0.5', 'Add(1)', '[]', repr('')])})"
        if c == 2:
            return f"max({r.choice([self.int_list(), self.n_list(), it])}" + \
                (f", default={self.small_int()})" if r.random() < 0.3 else ")")
        if c == 3:
            return f"min({self.n_list()}, key=lambda n: -n.v)" if r.random() < 0.5 \
                else f"min({it})"
        if c == 4:
            return f"sorted({r.choice([self.int_list(), self.n_list(), self.str_list(), it])}" + \
                (", reverse=True)" if r.random() < 0.3 else ")")
        if c == 5:
            return f"list(zip({it}, {self.iterable()}))"
        if c == 6:
            return f"list(enumerate({it}, {self.small_int()}))"
        if c == 7:
            return f"list(reversed({r.choice([self.int_list(), 'range(5)', self.word()])}))"
        if c == 8:
            return f"any({it})" if r.random() < 0.5 else f"all({it})"
        if c == 9:
            ctor = r.choice(['list', 'tuple', 'dict.fromkeys', 'set'])
            return f"sorted(set({it}), key=repr)" if ctor == 'set' else f"{ctor}({it})"
        if c == 10:
            return f"{self.word()}.{r.choice(['upper', 'lower', 'title', 'swapcase', 'casefold', 'capitalize', 'strip', 'isdigit', 'isalpha', 'isspace', 'isidentifier', 'splitlines', 'split'])}()"
        if c == 11:
            return f"{self.word()}.{r.choice(['find', 'rfind', 'count', 'startswith', 'endswith', 'index', 'rindex', 'partition', 'rpartition', 'split', 'rsplit', 'removeprefix', 'removesuffix'])}({self.word()})"
        if c == 12:
            return f"{self.word()}.{r.choice(['center', 'ljust', 'rjust', 'zfill', 'expandtabs'])}({r.choice([self.small_int(), 'Idx(6)', repr('x')])})"
        if c == 13:
            return f"{self.word()}.replace({self.word()}, {self.word()}, {self.small_int()})"
        if c == 14:
            return f"{self.word()}.join({self.str_list()})" if r.random() < 0.8 \
                else f"','.join({self.int_list()})"
        if c == 15:
            return f"{r.choice(['int', 'float'])}({r.choice([self.word(), repr(' 1_000 '), repr('0x1f'), repr('1e3'), repr('nan'), '2.5', 'Idx(4)'])})"
        if c == 16:
            return f"int({r.choice([repr('ff'), repr('0b101'), repr('z')])}, {r.choice(['16', '0', '36', '2'])})"
        if c == 17:
            return f"{repr('{} and {!r}')}.format({self.word()}, {self.word()})" if r.random() < 0.5 \
                else f"{repr('{0:>5}|{x}')}.format({self.small_int()}, x={self.word()})"
        if c == 18:
            return f"{self.word()}.encode({r.choice(['', repr('ascii'), repr('utf-16'), repr('latin-1')])})"
        if c == 19:
            return f"divmod({self.small_int()}, {r.choice([self.small_int(), '2.5'])})"
        if c == 20:
            return f"{r.choice(['abs', 'hex', 'callable'])}({r.choice([self.small_int(), '-2.5', 'Idx(3)', 'len'])})"
        if c == 21:
            return f"getattr({r.choice(['N(1)', self.word(), '[]'])}, {r.choice([repr('v'), repr('nope')])}" + \
                (", None)" if r.random() < 0.5 else ")")
        if c == 22:
            return f"hasattr({r.choice(['N(1)', '[]', 'It([])'])}, {r.choice([repr('v'), repr('append'), repr('x')])})"
        if c == 23:
            return f"issubclass({r.choice(['bool', 'N', 'int'])}, {r.choice(['int', 'object', '(str, int)'])})"
        if c == 24:
            return f"{self.int_list()}.{r.choice(['index', 'count'])}({self.small_int()})"
        if c == 25:
            return f"{self.word()}.translate({{97: 'A', 98: None}})"
        if c == 26:
            m = r.choice(['union', 'intersection', 'difference', 'symmetric_difference', 'issubset', 'issuperset', 'isdisjoint'])
            e = f"set({self.int_list()}).{m}({self.int_iterable()})"
            return e if m.startswith('is') else f"sorted({e}, key=repr)"
        if c == 27:
            m = r.choice(['copy', 'union', 'intersection', 'difference', 'symmetric_difference',
                          'issubset', 'issuperset', 'isdisjoint'])
            if m == 'copy':
                return f"sorted(frozenset({self.int_list()}).copy())"
            e = f"frozenset({self.int_list()}).{m}({self.int_list()})"
            return e if m.startswith('is') else f"sorted({e})"
        if c == 28:
            return f"range({self.small_int()}).{r.choice(['count', 'index'])}({self.small_int()})"
        if c == 29:
            return f"{r.choice(['sum', 'max', 'len', 'sorted', 'list'])}({r.choice(['', '1, 2, 3', '5', 'None'])})"
        if c == 30:
            return f"{self.word()}.{r.choice(['isprintable', 'isupper', 'islower', 'istitle', 'isalnum', 'isdecimal', 'isnumeric', 'isascii', 'lstrip', 'rstrip'])}()"
        if c == 31:
            return f"str.maketrans({r.choice([repr('ab'), '{97: 98}', repr('abc')])}, {r.choice([repr('xy'), repr('xyz'), 'None'])})" \
                if r.random() < 0.5 else f"{self.word()}.translate(str.maketrans('ab', 'BA'))"
        if c == 32:
            return f"{repr('{x}-{y}')}.format_map({{'x': {self.word()}, 'y': {self.small_int()}}})" \
                if r.random() < 0.7 else f"{repr('{x}')}.format_map({{}})"
        if c == 33:
            return f"tuple({self.int_list()}).{r.choice(['count', 'index'])}({self.small_int()})"
        if c == 34:
            return f"hash({r.choice([self.small_int(), '(1, 2)', 'N(3)', 'True', '2.5', '[]'])})"
        if c == 35:
            return f"(setattr({r.choice(['N(1)', '[]', 'It([])'])}, {r.choice([repr('v'), repr('w')])}, {self.small_int()}), 'set')"
        if c == 36:
            # User objects as set members and dict keys reach __hash__ and __eq__.
            return f"sorted({{N(1), N(2), N(1), N({self.small_int()})}}, key=lambda n: n.v)" \
                if r.random() < 0.5 else f"{{N(1): 'a', N(2): 'b'}}.get(N({r.choice(['1', '2', '3'])}))"
        if c == 37:
            return f"{self.small_int()} + Add({self.small_int()})" if r.random() < 0.5 \
                else f"sum([Add(1), Add(2)], {self.small_int()})"
        if c == 38:
            return f"list(Hint({r.randrange(0, 5)}))"
        # User iterables as pairs (a nested walk inside one step).
        return f"dict([It(['a', {self.small_int()}]), ('b', 2)])" if r.random() < 0.5 \
            else f"dict([{self.word()}])"

    def guarded(self, expr):
        self.emit("try:")
        self.depth += 1
        self.emit(f"print({expr})")
        self.depth -= 1
        self.emit("except Exception as e:")
        self.depth += 1
        self.emit("print(type(e).__name__, e)")
        self.depth -= 1

    # Statements on containers that the program keeps.
    def container_stmt(self):
        r = self.r
        if not self.vars or r.random() < 0.3:
            v = self.fresh()
            kind = r.choice(["list", "dict", "set"])
            if kind == "list":
                self.emit(f"{v} = {self.int_list()}")
            elif kind == "dict":
                self.emit(f"{v} = {{{', '.join(f'{self.small_int()}: {self.word()}' for _ in range(r.randrange(0, 4)))}}}")
            else:
                self.emit(f"{v} = set({self.int_list()})")
            self.vars.append((v, kind))
            return
        v, kind = r.choice(self.vars)
        if kind == "list":
            op = r.choice([f"append({self.small_int()})", f"extend({self.iterable()})",
                           f"insert({self.small_int()}, {self.small_int()})", "pop()",
                           f"pop({self.small_int()})", f"remove({self.small_int()})", "sort()",
                           "sort(reverse=True)", "reverse()", "clear()", "copy()"])
        elif kind == "dict":
            op = r.choice([f"get({self.small_int()})", f"pop({self.small_int()})",
                           f"setdefault({self.small_int()}, {self.word()})",
                           f"update({{{self.small_int()}: 'u'}})", "popitem()", "clear()",
                           "copy()", f"update([({self.small_int()}, 'p')])"])
            if r.random() < 0.3:
                self.guarded(f"(list({v}.keys()), list({v}.values()), list({v}.items()))")
                return
        else:
            op = r.choice([f"add({self.small_int()})", f"discard({self.small_int()})",
                           f"remove({self.small_int()})", "pop()", "clear()", "copy()",
                           f"update({self.int_iterable()})", f"difference_update({self.int_list()})",
                           f"intersection_update({self.int_list()})",
                           f"symmetric_difference_update({self.int_list()})"])
        self.guarded(f"{v}.{op}")
        self.guarded(f"sorted({v})" if kind == "set" else v)

    def mutate_while_iterating(self):
        r = self.r
        v = self.fresh()
        kind = r.choice(["list", "dict", "set"])
        if kind == "list":
            self.emit(f"{v} = {self.int_list()}")
            body = f"{v}.append(x)"
        elif kind == "dict":
            self.emit(f"{v} = {{1: 'a', 2: 'b'}}")
            body = f"{v}[x + 10] = 'z'"
        else:
            self.emit(f"{v} = {{1, 2, 3}}")
            body = f"{v}.add(x + 10)"
        self.emit("try:")
        self.depth += 1
        self.emit("count = 0")
        self.emit(f"for x in {v}:")
        self.depth += 1
        self.emit('print("loop", x)')
        self.emit("count += 1")
        self.emit("if count > 4:")
        self.emit("    break")
        self.emit(body)
        self.depth -= 2
        self.emit("except Exception as e:")
        self.emit("    print(type(e).__name__, e)")

    def block(self, size):
        for _ in range(size):
            c = self.r.randrange(10)
            if c < 4:
                self.guarded(self.call())
            elif c < 6:
                self.container_stmt()
            elif c == 6:
                self.mutate_while_iterating()
            elif c == 7 and self.depth < 2:
                self.emit(f"for i in range({self.r.randrange(1, 4)}):")
                self.depth += 1
                self.emit('print("for", i)')
                self.block(self.r.randrange(1, 3))
                self.depth -= 1
            elif c == 8 and self.depth < 2:
                self.emit(f"k = {self.r.randrange(1, 4)}")
                self.emit("while k > 0:")
                self.depth += 1
                self.emit('print("while", k)')
                self.emit("k -= 1")
                self.emit("try:")
                self.depth += 1
                self.emit('print("try")')
                self.block(1)
                self.depth -= 1
                self.emit("except Exception as e:")
                self.emit("    print(type(e).__name__)")
                self.depth -= 1
            elif self.depth < 2:
                self.emit("try:")
                self.emit(f"    cond = {self.call()}")
                self.emit("except Exception as e:")
                self.emit("    print(type(e).__name__, e)")
                self.emit("    cond = False")
                self.emit("if cond:")
                self.depth += 1
                self.emit('print("then")')
                self.block(1)
                self.depth -= 1
                self.emit("else:")
                self.depth += 1
                self.emit('print("else")')
                self.depth -= 1
            else:
                self.guarded(self.call())

    def program(self):
        self.emit("events = []")
        for name in sorted(CLASSES):
            self.lines.extend(CLASSES[name].rstrip("\n").split("\n"))
        self.emit('print("start")')
        self.block(self.r.randrange(4, 9))
        self.emit('print("events", events)')
        return "\n".join(self.lines) + "\n"


def main():
    p = argparse.ArgumentParser()
    p.add_argument("out")
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--count", type=int, default=500)
    a = p.parse_args()
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    for i in range(a.count):
        pid = f"gen_{a.seed}_{i}"
        text = Gen(random.Random(f"{a.seed}:{i}")).program()
        (out / f"{pid}.py").write_text(text)
        print(pid)


if __name__ == "__main__":
    main()

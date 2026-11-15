# Loop exits, run.  The functions below have loops that end by exhaustion, return, raise or break,
# also through finally bodies, with bodies and nested loops, or that raise from the loop's guard,
# iterator or target, and bodies that continue through a finally body or catch a StopIteration.
# Every function is called, so that the differential test runs these exits against CPython.
def cleanup(log):
    log += ["c"]

def ret_in_for(xs, log):
    for x in xs:
        if x == 2:
            return x
    else:
        return -1
    return 0

def ret_in_while_finally(n, log):
    i = 0
    while True:
        try:
            i = i + 1
            if i == n:
                return i
        finally:
            cleanup(log)

def raise_out(xs, log):
    try:
        for x in xs:
            if x == 3:
                raise ValueError(x)
            log += [x]
    except ValueError as e:
        return ("caught", e.args[0])
    return "none"

def break_finally(xs, log):
    for x in xs:
        try:
            if x == 2:
                break
            log += [x]
        finally:
            cleanup(log)
    else:
        log += ["else"]
    return x

def continue_finally(xs, log):
    t = 0
    for x in xs:
        try:
            if x % 2 == 0:
                continue
            t = t + x
        finally:
            log += [x]
    return t

def nested_ret(outer, inner, log):
    for p in outer:
        try:
            for q in inner:
                try:
                    if p * q == 6:
                        return (p, q)
                finally:
                    log += [q]
        finally:
            cleanup(log)
    return None

def exc_through_two_loops(log):
    try:
        for i in [1, 2]:
            j = 0
            while j < 3:
                j = j + 1
                if i == 2 and j == 2:
                    raise KeyError(i * 10 + j)
                log += [(i, j)]
    except KeyError as e:
        return e.args[0]

def stop_inside(it, log):
    for x in [1, 2, 3]:
        try:
            y = next(it)
        except StopIteration:
            log += ["stop"]
            break
        log += [y]
    else:
        log += ["else"]
    return x

for f, a in [(ret_in_for, ([1, 2, 3],)), (ret_in_for, ([5],)), (ret_in_while_finally, (3,)),
             (raise_out, ([1, 2, 3, 4],)), (raise_out, ([1],)), (break_finally, ([1, 2, 3],)),
             (break_finally, ([1],)), (continue_finally, ([1, 2, 3, 4, 5],)),
             (nested_ret, ([1, 2, 3], [1, 3, 5])), (nested_ret, ([7], [7])),
             (exc_through_two_loops, ()), (stop_inside, (iter([9]),))]:
    log = []
    r = f(*a, log)
    print(f.__name__, r, log)

class Bad:
    def __init__(self):
        self.n = 0
    def __iter__(self):
        return self
    def __next__(self):
        self.n = self.n + 1
        if self.n == 3:
            raise ValueError(self.n)
        return self.n

class Flag:
    def __init__(self, k):
        self.k = k
    def __bool__(self):
        if self.k == 0:
            raise KeyError("guard")
        self.k = self.k - 1
        return True

class Ctx:
    def __init__(self, log):
        self.log = log
    def __enter__(self):
        self.log += ["in"]
        return self
    def __exit__(self, t, v, tb):
        self.log += ["out"]
        return False

def next_raises(log):
    try:
        for x in Bad():
            log += [x]
    except ValueError as e:
        return ("next", e.args[0])

def target_raises(log):
    try:
        for a, b in [(1, 2), (3,)]:
            log += [a + b]
    except ValueError:
        return "unpack"

def guard_raises(log):
    f = Flag(2)
    try:
        while f:
            log += ["w"]
    except KeyError as e:
        return e.args[0]

def handler_raises(log):
    try:
        for x in [1, 2]:
            try:
                raise TypeError(x)
            except TypeError:
                log += ["h"]
                raise IndexError(x)
    except IndexError as e:
        return e.args[0]

def with_exits(log):
    for x in [1, 2, 3, 4]:
        with Ctx(log):
            if x == 1:
                continue
            if x == 3:
                break
            log += [x]
    for y in [5, 6]:
        with Ctx(log):
            if y == 6:
                return y

def while_break_else(n, log):
    i = 0
    while i < 5:
        i = i + 1
        if i == n:
            break
    else:
        log += ["else"]
    return i

for f, a in [(next_raises, ()), (target_raises, ()), (guard_raises, ()), (handler_raises, ()),
             (with_exits, ()), (while_break_else, (2,)), (while_break_else, (9,))]:
    log = []
    r = f(*a, log)
    print(f.__name__, r, log)

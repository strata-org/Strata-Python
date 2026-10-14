# try/finally: what runs, and which exception is being handled in the finally body.
import sys

def note(x):
    return x

def reraise(f):
    try:
        f()
    finally:
        raise  # on the exceptional path, what f raised; otherwise RuntimeError

def handled(f):
    try:
        f()
    finally:
        note(sys.exc_info()[1])  # what f raised, or None

def return_drops(f):
    try:
        f()
    finally:
        return 1  # drops what f raised, and restores the exception handled before

def break_drops(f, xs):
    for x in xs:
        try:
            f()
        finally:
            break  # drops what f raised
    return 0

def continue_in_finally(f, xs):
    for x in xs:
        try:
            f()
        finally:
            note(x)
            continue
    return 0

def superseded(f):
    try:
        f()
    finally:
        raise ValueError("new")  # its __context__ is what f raised

def in_handler(f):
    try:
        raise KeyError("outer")
    except KeyError as e:
        try:
            f()
        finally:
            note(e)  # a failure here goes through the clause's clear block
    return 0

def all_parts(f):
    try:
        r = f()
    except KeyError:
        r = 1
    else:
        r = 2
    finally:
        note(r)
    return r

def nested(f):
    try:
        try:
            return f()
        finally:
            note(1)
    finally:
        note(2)

def finally_in_finally(f, g):
    try:
        f()
    finally:
        try:
            g()
        finally:
            note(1)  # a failure here supersedes in both finally bodies

def loop_in_finally(f, xs):
    try:
        f()
    finally:
        for x in xs:  # what the loop raises supersedes what f raised
            note(x)

def return_in_handler(f):
    try:
        raise KeyError("k")
    except KeyError as e:
        try:
            f()
        finally:
            return e  # leaves the finally body, then the handler, and unbinds e

class Body:
    try:
        v = note(1)
    finally:
        w = 2

try:
    note(1)
finally:
    note(2)

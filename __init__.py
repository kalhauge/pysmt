
from .theories import ints, core
from .solver import *
from .expression import *

not_ = lambda x: core.Not.from_values(x).simplify()

add = ints.Add.from_values
sub = ints.Sub.from_values
mul = ints.Mul.from_values
div = ints.Div.from_values
mod = ints.Mod.from_values
eq  = ints.Eq.from_values
lt  = ints.Lt.from_values
gt  = ints.Gt.from_values
ge  = ints.Ge.from_values
le  = ints.Le.from_values
ne  = lambda fst, snd: not_(eq(fst, snd))

next = lambda fst, snd: eq(add(fst, 1), snd)

true = core.Bool().get_value(True)
false = core.Bool().get_value(False)

def all(terms):
    ts = list(terms)
    return {
        0 : lambda *x: true,
        1 : lambda *x: ts[0]
    }.get(len(ts), core.And.from_values)(*ts)

def any(terms):
    ts = list(terms)
    return {
        0 : lambda *x: false,
        1 : lambda *x: ts[0]
    }.get(len(ts), core.Or.from_values)(*ts)

order = ints.Order.from_values




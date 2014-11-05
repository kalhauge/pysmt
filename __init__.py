
from .solver import *
from .arithmetic import *

BINARY = dict(
    add=Add, 
    sub=Sub, 
    mul=Mul, 
    div=FloorDiv,
    eq=Eq,
    lt=Lt,
    gt=Gt,
    ge=Ge,
    le=Le,
)
binary = lambda opr, fst, snd: BINARY[opr].from_values(fst, snd)

add = Add.from_values
sub = Sub.from_values
mul = Mul.from_values
div = FloorDiv.from_values
eq  = Eq.from_values
lt  = Lt.from_values
gt  = Gt.from_values
ge  = Ge.from_values
le  = Le.from_values


next = lambda fst, snd: eq(add(fst, 1), snd)

true = Value.from_value(True)
false = Value.from_value(False)

def all(terms):
    ts = list(terms)
    return {
        0 : lambda x: true,
        1 : lambda x: ts[0]
    }.get(len(ts), All)(ts)

def any(terms):
    ts = list(terms)
    return {
        0 : lambda x: false,
        1 : lambda x: ts[0]
    }.get(len(ts), Any)(ts)

order = Order.from_values


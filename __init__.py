
from .solver import *
from .arithmetic import *

not_ = Not.from_values

UNARY = {
    'not' : not_
}

unary = lambda opr, val: BINARY[opr](val)

add = Add.from_values
sub = Sub.from_values
mul = Mul.from_values
div = FloorDiv.from_values
eq  = Eq.from_values
lt  = Lt.from_values
gt  = Gt.from_values
ge  = Ge.from_values
le  = Le.from_values
ne  = lambda fst, snd: not_(eq(fst, snd))

BINARY = dict(
    add = add ,
    sub = sub ,
    mul = mul ,
    div = div ,
    eq  = eq  ,
    lt  = lt  ,
    gt  = gt  ,
    ge  = ge  ,
    le  = le  ,
    ne  = ne  ,
)

binary = lambda opr, fst, snd: BINARY[opr](fst, snd)

next = lambda fst, snd: eq(add(fst, 1), snd)

function = DynamicOperator.from_values


true = Value.from_value(True)
false = Value.from_value(False)

def all(terms):
    ts = list(terms)
    return {
        0 : lambda *x: true,
        1 : lambda *x: ts[0]
    }.get(len(ts), All)(*ts)

def any(terms):
    ts = list(terms)
    return {
        0 : lambda *x: false,
        1 : lambda *x: ts[0]
    }.get(len(ts), Any)(*ts)

order = Order.from_values



import operator
import re

from pysmt.expression import BinaryOperator, UnaryOperator, Operator, Type

class Int(Type):
    
    re_number = re.compile('(\(- (?P<minus>[0-9]+)\))|(?P<plus>[0-9]+)')

    def __new__(cls):
        if not hasattr(cls, '_instance'):
            cls._instance = super().__new__(cls)
        return cls._instance

    def compile_smt2(self):
        return 'Int'

    def present_smt2(self, value):
        return str(value)
    
    def parse_value(self, value):
        d = self.re_number.match(value).groupdict()
        value = -int(d['minus']) if d['minus'] else int(d['plus'])
        return value

def pairwise(iterable):
    a, b = tee(iterable)
    next(b, None)
    return zip(a, b)

class Order(Operator):
    opr = lambda *args: all(a < b for a, b in pairwise(args))
    smt2_opr = '<'

class Add(BinaryOperator):
    """ Adds the first and the second value """
    opr = operator.add
    smt2_opr = '+'

class Sub(BinaryOperator):
    """ Substracts the first and the second value """
    opr = operator.sub
    smt2_opr = '-'
         
class Mul(BinaryOperator):
    """ Multiplies the first and the second value """
    opr = operator.mul
    smt2_opr = '*'

class Div(BinaryOperator):
    opr = operator.floordiv
    smt2_opr = 'div'

class Mod(BinaryOperator):
    opr = operator.mod
    smt2_opr = 'mod'

class Eq(BinaryOperator):
    opr = operator.eq
    smt2_opr = '='

class Ge(BinaryOperator):
    opr = operator.ge
    smt2_opr = '>='

class Le(BinaryOperator):
    opr = operator.le
    smt2_opr = '<='

class Gt(BinaryOperator):
    opr = operator.gt
    smt2_opr = '>'

class Lt(BinaryOperator):
    opr = operator.lt
    smt2_opr = '<'


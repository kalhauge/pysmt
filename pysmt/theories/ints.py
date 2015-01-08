import operator
import re

from pysmt.expression import BinaryOperator, UnaryOperator, Operator, Type
from pysmt.theories.core import BoolOperator
from pysmt.utils import pairwise

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

class IntOperator:
    class_type = Int()

class Add(IntOperator, BinaryOperator):
    """ Adds the first and the second value """
    opr = operator.add
    smt2_opr = '+'

class Sub(IntOperator, BinaryOperator):
    """ Substracts the first and the second value """
    opr = operator.sub
    smt2_opr = '-'
         
class Mul(IntOperator, BinaryOperator):
    """ Multiplies the first and the second value """
    opr = operator.mul
    smt2_opr = '*'

class Div(IntOperator, BinaryOperator):
    opr = operator.floordiv
    smt2_opr = 'div'

class Mod(IntOperator, BinaryOperator):
    opr = operator.mod
    smt2_opr = 'mod'

class Order(BoolOperator, Operator):
    opr = lambda *args: all(a < b for a, b in pairwise(args))
    smt2_opr = '<'

class Eq(BoolOperator, BinaryOperator):
    opr = operator.eq
    smt2_opr = '='

class Ge(BoolOperator, BinaryOperator):
    opr = operator.ge
    smt2_opr = '>='

class Le(BoolOperator, BinaryOperator):
    opr = operator.le
    smt2_opr = '<='

class Gt(BoolOperator, BinaryOperator):
    opr = operator.gt
    smt2_opr = '>'

class Lt(BoolOperator, BinaryOperator):
    opr = operator.lt
    smt2_opr = '<'


"""
This files contains the bitvector system of smt
"""
import operator

from pysmt.expression import Expression, Operator, BinaryOperator, UnaryOperator, Type

class BitVec (Type):
    
    def __new__(cls, size):
        if not hasattr(cls, '_instances'):
            cls._instances = dict()
        if not size in cls._instances:
            instance = super().__new__(cls)
            cls._instances[size] = instance
            instance.size = size
        return cls._instances[size]
    
    def compile_smt2(self):
        return "(_ BitVec {})".format(self.size)

    def present_smt2(self, value):
        absvalue = abs(value) + (2**31 if value < 0 else 0) 
        if self.size % 4 != 0:
            formating = ':0{0}b'.format(self.size -1)
            return '#b{{{0}}}'.format(formating).format(absvalue)
        else:
            formating = '0:0{0}x'.format(self.size // 4)
            return '#x{{{0}}}'.format(formating).format(absvalue)

    def parse_value(self, string):
        return (-1 if int(string[2]) == 1 else 1) * int(string[3:], 2)


class Concat (BinaryOperator):
    smt2_opr = 'concat'

class And (BinaryOperator):
    smt2_opr='bvand'

class Or (BinaryOperator):
    smt2_opr='bvor'

class Add (BinaryOperator):
    smt2_opr='bvadd'

class Sub (BinaryOperator):
    smt2_opr='bvadd'

class Mul (BinaryOperator):
    smt2_opr='bvmul'

class Udiv (BinaryOperator):
    smt2_opr='bvudiv'

class Rem (BinaryOperator):
    smt2_opr='bvrem'

class Shl (BinaryOperator):
    opr = operator.lshift 
    smt2_opr='bvshl'

class Lshr (BinaryOperator):
    opr = operator.rshift 
    smt2_opr='bvlshr'

class Slt (BinaryOperator):
    smt2_opr='bvslt'

class Sle (BinaryOperator):
    smt2_opr='bvsle'

class Sgt (BinaryOperator):
    smt2_opr='bvsgt'

class Sge (BinaryOperator):
    smt2_opr='bvsge'

class Not (UnaryOperator):
    smt2_opr = 'bvnot'

class Neg (UnaryOperator):
    smt2_opr = 'bvneg'

class Eq (BinaryOperator):
    opr = operator.eq
    smt2_opr = '='

def test_present():
    bv = BitVec(8)
    assert bv.present(6) == '#x6'



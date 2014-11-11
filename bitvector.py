"""
This files contains the bitvektor system of smt
"""

from .expression import Expression, Operator, BinaryOperator, UnaryOperator, Type

class BitVec (Type):
    
    def __init__(self, size):
        self.size = size

    def compile_smt2(self):
        return "(_ BitVec {})".format(self)

    def present_smt2(self, value):
        if self.size % 8 != 0:
            formating = '0:0{0}b'.format(self.size)
            return '#b{{{0}}}'.format(formating).format(value)
        else:
            formating = '0:0{0}x'.format(self.size//8)
            return '#x{{{0}}}'.format(formating).format(value)


class Concat(BinaryOperator):
    smt2_opr = 'concat'

class And (BinaryOperator):
    smt2_opr='bvand'

class Or (BinaryOperator):
   smt2_opr='bvor'

class Add (BinaryOperator):
   smt2_opr='bvadd'

class Mul (BinaryOperator):
   smt2_opr='bvmul'

class Udiv (BinaryOperator):
   smt2_opr='bvudiv'

class Rem (BinaryOperator):
   smt2_opr='bvrem'

class Shl (BinaryOperator):
   smt2_opr='bvshl'

class Lshr (BinaryOperator):
   smt2_opr='bvlshr'

class Ult (BinaryOperator):
   smt2_opr='bvult'

class Not(UnaryOperator):
    smt2_opr = 'bvnot'

class Neg(UnaryOperator):
    smt2_opr = 'bvneg'

def test_present():
    bv = BitVec(8)
    assert bv.present(6) == '#x6'



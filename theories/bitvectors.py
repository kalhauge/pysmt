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
        binval = value & ( 2**self.size -1 )
        if self.size % 4 != 0:
            formating = ':0{0}b'.format(self.size)
            smt2 = '#b{{{0}}}'.format(formating).format(binval)
        else:
            formating = '0:0{0}x'.format(self.size // 4)
            smt2 = '#x{{{0}}}'.format(formating).format(binval)
        return smt2

    def parse_value(self, string):
        binary_string = string[2:]
        if len(binary_string) != self.size:
            raise ValueError(
                'Bad length of binary string {} != {} {!r}'.format(
                    len(binary_string),
                    self.size,
                    binary_string
            ))
        a = int(binary_string, 2)
        if string[2] == '1':
            return -1 - (a ^ ( 2**self.size -1 ))
        else:
            return a


class Concat (BinaryOperator):
    smt2_opr = 'concat'

class And (BinaryOperator):
    smt2_opr='bvand'

class Or (BinaryOperator):
    smt2_opr='bvor'

class Add (BinaryOperator):
    smt2_opr='bvadd'

class Sub (BinaryOperator):
    smt2_opr='bvsub'

class Mul (BinaryOperator):
    smt2_opr='bvmul'

class Udiv (BinaryOperator):
    smt2_opr='bvudiv'

class Sdiv (BinaryOperator):
    smt2_opr='bvsdiv'

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



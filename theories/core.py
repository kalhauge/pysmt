
import operator

from pysmt.expression import Expression, Operator, BinaryOperator, UnaryOperator, Type

class Bool(Type):
    
    def __new__(cls):
        if not hasattr(cls, '_instance'):
            cls._instance = super().__new__(cls)
        return cls._instance
    
    def compile_smt2(self):
        return 'Bool'

    def present_smt2(self, value): 
        return 'true' if value else 'false'

class And(Operator):
    opr = all
    smt2_opr = 'and'

class Or(Operator):
    opr = any
    smt2_opr = 'or'

class Not(UnaryOperator):
    opr = operator.not_
    smt2_opr = 'not'

    def simplify(self):
        if isinstance(self.value, Not):
            return self.value.value.simplify()
        else:
            return self


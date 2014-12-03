
import operator

from pysmt.expression import Operator, BinaryOperator, UnaryOperator, Type

class Bool(Type):
    
    def __new__(cls):
        if not hasattr(cls, '_instance'):
            cls._instance = super().__new__(cls)
        return cls._instance
    
    def compile_smt2(self):
        return 'Bool'

    def present_smt2(self, value): 
        return 'true' if value else 'false'

class BoolOperator:
    class_type = Bool()

class And(BoolOperator, Operator):
    opr = all
    smt2_opr = 'and'

    def simplify(self):
        newargs = []
        for arg in self.args:
            newarg = arg.simplify()
            if isinstance(newarg, And):
                total.extend(newarg.args)
            elif isinstance(newarg, Value) and not newarg.value:
                return newarg.value
            else:
                newargs.append(newarg)
        if newargs != self.args:
            return And(*total)

class Or(BoolOperator, Operator):
    opr = any
    smt2_opr = 'or'

    def simplify(self):
        newargs = []
        for arg in self.args:
            newarg = arg.simplify()
            if isinstance(newarg, Or):
                total.extend(newarg.args)
            elif isinstance(newarg, Value) and newarg.value:
                return newarg.value
            else:
                newargs.append(newarg)
        if newargs != self.args:
            return Or(*total)

class Not(BoolOperator, UnaryOperator):
    opr = operator.not_
    smt2_opr = 'not'

    def simplify(self):
        if isinstance(self.value, Not):
            return self.value.value.simplify()
        else:
            return self


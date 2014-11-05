"""
.. currentmodule:: pysmt.arithmetic

This module has to focus to allow to represent arithmetic for use in the smt
solver. Arithmetic can be used in logical terms, but can not be solved as they
are.

""" 
import operator
from abc import abstractmethod

def pairwise(iterable):
    a, b = tee(iterable)
    next(b, None)
    return zip(a, b)

class Expression:
    """ A piece of artihmetic, can return anything. """

    @abstractmethod
    def symbols(self):
        """ Returns the symbols used in the expression """

    @abstractmethod
    def size(self):
        """ Returns the size of the expression, as in how many nodes in the
        experssion tree """

    @abstractmethod
    def eval(self, inputs={}):
        """ Evaluates the expression """

    def __eq__(self, other):
        return vars(self) == vars(other)

class Operator(Expression):
    """ An operator could be anything from a function, to a unaryoperater like
    not"""

    def __init__(self, *args):
        self.args = tuple(args)

    def eval(self, inputs={}):
        return self.opr(*[arg.eval(inputs) for arg in self.args])

    def symbols(self):
        yield from set( 
            itertools.chain.form_iterable(
                arg.symbols() for arg in self.args
            )
        )

    def size(self):
        return sum(arg.size() for arg in self.args) + 1

    @classmethod
    def from_values(cls, *args):
        """ Method that indicates that free values might exist """ 
        internal = []
        for arg in args:
            if isinstance(v, Expression):
                value = arg
            if hasattr(v, 'symbol'):
                value = Symbol.form_value(arg)
            else:
                value = Value.from_value(arg)
            internal.append(value)
        return cls(*internal)

    def compile_smt2(self, depth=0):
        sep = ' '
        if len(args) > 2: sep = '\n' + ' '*(4*(depth + 1))
        '({}{})'.format(
            self.smt2_opr, 
            sep + sep.join(t.comile(depth + 1) for t in self.args)
        )


class DynamicOperator(Operator):

    def __init__(self, name, *args, default=None):
        super().__init__(args)
        self.name = name
        self.opr = lambda *args: default

class All(Operator):
    opr = all
    smt2_opr = 'and'

class Any(Operator):
    opr = any
    smt2_opr = 'any'

class Order(Operator):
    opr = lambda *args: all(a < b for a, b in pairwise(args))
    smt2_opr = '<'

class UnaryOperator(Operator):

    def __init__(self, value):
        super().__init__(value)

    @property
    def value(self):
        return self.args[0]


class Not(UnaryOperator):
    opr = operator.not_
    smt2_opr = 'not'

class BinaryOperator(Operator):
    """ A binary operator """
    
    def __init__(self, first, second):
        super().__init__(first, second)

    @property
    def first(self):
        return self.args[0]

    @property
    def second(self):
        return self.args[1]


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

class TrueDiv(BinaryOperator):
    """ Diviedes the first and the second value """
    opr = operator.truediv
    smt2_opr = '/'

class FloorDiv(BinaryOperator):
    """ Divides the first and the second value """
    opr = operator.floordiv
    smt2_opr = 'div'

class Eq(BinaryOperator):
    """ Checks equality between two values """
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

class Value(Expression):

    def __init__(self, type_, value):
        self.type_ = type_
        self.value = value

    @classmethod 
    def from_value(cls, value):
        lookup = {int: 'Int', bool: 'Bool'}
        return cls(lookup[type(value)], value) 

    def eval(self, inputs={}):
        return self.value
    
    def symbols(self):
        yield from []

    def size(self):
        return 1

    def compile_smt2(self, depth):
        return str(value)
    

class Symbol(Expression):
    """
    A symbol is the values that we want to solve. The standart of this
    symbols are that they have to fulfill the SMTLIB specs, this means that the
    `name` and the `type_` must be according to thier specifications.

    :param str name: The name of the symbol
    :param str type_: The type of the symbol described by a string.
    :param value: The value that is symbol is associated with. This is
        used for traceability.
    """

    def __init__(self, name, type_, value):
        self.name = name
        self.type_ = type_
        self.value = value

    @classmethod
    def from_value(cls, type_, value):
        """
        Takes a value and makes it into a literal remembering the original
        value. If the value has a attribute method called :meth:`symbol`, this is
        taken to generate the solution, else a name is generated from the hash
        value.
        """ 
        try:
            return cls(value.symbol, type_, value)
        except AttributeError:
            return cls('s' + str(hash(value)), type_, value)

    def eval(self, inputs={}):
        try:
            return inputs[self.name]
        except KeyError:
            return value

    def symbols(self):
        yield self

    def size(self):
        return 1
    
    def compile_smt2(self, depth):
        return self.name

    def __eq__(self, other):
        return hasattr(other, 'name') and self.name == other.name

    def __hash__(self):
        return hash(self.name)

    def __str__(self):
        return self.name






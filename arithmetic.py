"""
.. currentmodule:: pysmt.arithmetic

This module has to focus to allow to represent arithmetic for use in the smt
solver. Arithmetic can be used in logical terms, but can not be solved as they
are.

""" 
import operator
from abc import abstractmethod


class Expression:
    """ A piece of artihmetic """

    @abstractmethod
    def symbols(self):
        """ Returns the symbols used in the expression """

    @abstractmethod
    def size(self):
        """ Returns the size of the expression, as in how many nodes in the
        experssion tree """

class BinaryOperator(Expression):
    """ A binary operator """

    def __init__(self, first, second):
        self.first = first
        self.second = second

    def eval(self, inputs={}):
        return self.opr(self.first.eval(inputs), self.second.eval(inputs))

    def symbols(self):
        yield from self.first.symbols()
        yield from self.second.symbols()

    def size(self):
        return self.first.size() + self.second.size() + 1

class Add(BinaryOperator):
    """ Adds the first and the second value """
    opr = operator.add

class Sub(BinaryOperator):
    """ Substracts the first and the second value """
    opr = operator.sub
         
class Mul(BinaryOperator):
    """ Multiplies the first and the second value """
    opr = operator.mul

class TrueDiv(BinaryOperator):
    """ Diviedes the first and the second value """
    opr = operator.truediv

class FloorDiv(BinaryOperator):
    """ Diviedes the first and the second value """
    opr = operator.floordiv

class Value(Expression):

    def __init__(self, type_, value):
        self.type_ = type_
        self.value = value

    @classmethod 
    def from_value(cls, value):
        lookup = {int: 'Int'}
        return cls(lookup[type(value)], value) 

    def eval(self, inputs={}):
        return self.value
    
    def symbols(self):
        yield from []

    def size(self):
        return 1
    

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

    def __eq__(self, other):
        return self.name == other.name

    def __hash__(self):
        return hash(self.name)

    def __str__(self):
        return self.name



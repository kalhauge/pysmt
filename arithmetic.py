"""
.. currentmodule:: pysmt.arithmetic

This module has to focus to allow to represent arithmetic for use in the smt
solver. Arithmetic can be used in logical terms, but can not be solved as they
are.

""" 
from .expression import Expression, Operator, BinaryOperator, UnaryOperator, Type

import operator
import itertools
from functools import partial
from abc import abstractmethod



class DynamicOperator(Operator):

    def __init__(self, name, default, *args):
        super().__init__(*args)
        self.name = name
        self.opr = lambda *args: default
        self.smt2_opr = self.name

    @classmethod 
    def from_values(cls, name, default, *args):
        return cls(name, default, *list(map(from_value, args)))

    def compile_smt2(self, depth=0):
        return Value.from_value(self.opr(*self.args)).compile_smt2(depth)
    

class Memory(Expression):

    def __init__(self, name):
        self.name = name

    def eval(self, inputs={}):
        return self.name
    
    def compile_smt2(self, depth=0):
        raise NotImplementedError('Can not compile to smt2')

    def __str__(self):
        return '(mem {})'.format(self.name)

    def __hash__(self):
        return hash(self.name)


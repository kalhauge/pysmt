"""
Logic
=====

.. currentmodule:: pysmt.logic

This file descripes the fundamental partial order logic, as used in this module.
"""

import itertools

from functools import partial
from abc import abstractmethod
from collections import namedtuple

from .arithmetic import Symbol


class Term:
    """ A piece of logic """

    @abstractmethod
    def symbols(self):
        """ Returns the symbols used in the term """

    @abstractmethod
    def size(self):
        """ Returns the size of the term, as in how many nodes in the term tree
        """

class All(Term):
    """ 
    All subterms must be true.
   
    .. attribute:: terms 
        
        The subterms that must be true. 
    """

    def __init__(self, terms):
        self.terms = list(terms) 
        assert len(self.terms) > 1, '\n'.join(map(str, self.terms))

    def symbols(self):
        yield from set(
            itertools.chain.from_iterable(
                term.symbols() for term in self.terms
            )
        )
   
    def size(self):
        return 1 + sum(t.size() for t in self.terms) 
        

class Any(Term):
    """ 
    Any of the subterms must be true.
   
    .. attribute:: terms 
    
        The subterms that must be true. 
    """

    def __init__(self, terms):
        self.terms = list(terms)
        assert len(self.terms) > 1

    def symbols(self):
        yield from set(
            itertools.chain.from_iterable(
                term.symbols() for term in self.terms
            )
        )
   
    def size(self):
        return 1 + sum(t.size() for t in self.terms) 

class Order(tuple, Term):
    """ 
    All the symbols must be ordered.
   
    .. attribute:: ordered_symbols

        The symbols must be ordered and givven values from small to large.
    """
   
    def symbols(self):
        yield from set(
            itertools.chain.from_iterable(
                expr.symbols() for expr in self
            )
        )
    
    @classmethod
    def from_values(cls, *values, type='Int'):
        return cls(map(partial(Symbol.from_value, type), values))
  
    def size(self):
        return 1 + sum(exp.size() for exp in self)

    def __repr__(self):
        return "Order({})".format(super().__repr__())

    def __str__(self):
        return ' < '.join(map(str, self))

class Next(Term):
    """
    A next term is true if the O(e1) + 1 = O(e2)

    """
    
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def symbols(self):
        yield from set(
            itertools.chain(
                self.e1.symbols(),
                self.e2.symbols()
            )
         )
    
    @classmethod
    def from_values(cls, e1, e2, type_='Int'):
        lit = partial(Symbol.from_value, type_)
        return cls(lit(e1), lit(e2))

    def size(self):
        return 3

class Eq(Term):
    """
    A next term is true if the O(e1) = O(e2)

    """
    
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def symbols(self):
        yield from (self.e1, self.e2)
    
    @classmethod
    def from_values(cls, e1, e2, type_='Int'):
        lit = partial(Symbol.from_value, type_)
        return cls(lit(e1), lit(e2))

    def size(self):
        return 3

class Boolean(Term):
    """
    Eighter True or False, depending on the value.
    """

    def __init__(self, value):
        self.value = value

    def symbols(self):
        yield from []

    def size(self):
        return 1

class Not(Term):

    def __init__(self, subterm):
        self.subterm = subterm

    def symbols(self):
        yield from self.subterm.symbols()

    def size(self):
        return 1 + self.subterm.size()

true = Boolean(True)
false = Boolean(False)

def all(terms):
    ts = list(terms)
    return {
        0 : lambda ts: true,
        1 : lambda ts: ts[0]
    }.get(len(ts), All)(ts)

def any(terms):
    ts = list(terms)
    return {
        0 : lambda ts: false,
        1 : lambda ts: ts[0]
    }.get(len(ts), Any)(ts)

order = Order.from_values
next = Next.from_values
not_ = Not 
eq = Eq.from_values



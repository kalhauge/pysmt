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

class Literal(namedtuple('Literal', ['name', 'type_', 'value'])):
    """
    A litteral is the values that we want to solve. The standart of this
    literals are that they have to fulfill the SMTLIB specs, this means that the
    name and the type_ must be according to thier specifications.

    :param str name: The name of the litteral.
    :param str type_: The type of the literal described by a string.
    :param str value: The value that is litteral is associated with. This is
        used for traceability.
    """
    literals = {}
    @classmethod
    def literalize(cls, type_, value):
        """
        Takes a value and makes it into a literal remembering the original
        value. If the value has a method called :meth:`rep`, this is called to
        generate the solution, else a name is generated from the hash value.
        """ 
        try:
            literal = cls.literals[value]
        except KeyError:
            literal = cls(value._rep, type_, value)
            cls.literals[value] = literal
        return literal

class Term:
    """ A piece of logic """

    @abstractmethod
    def literals(self):
        """ Returns the literals used in the term """

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
        assert len(self.terms) > 1

    def literals(self):
        yield from set(
            itertools.chain.from_iterable(
                term.literals() for term in self.terms
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

    def literals(self):
        yield from set(
            itertools.chain.from_iterable(
                term.literals() for term in self.terms
            )
        )
   
    def size(self):
        return 1 + sum(t.size() for t in self.terms) 

class Order(tuple, Term):
    """ 
    All the literals must be ordered.
   
    .. attribute:: ordered_literals

        The literals must be ordered and givven values from small to large.
    """
   
    def literals(self):
        yield from self
    
    @classmethod
    def from_values(cls, *values, type='Int'):
        return cls(map(partial(Literal.literalize, type), values))
  
    def size(self):
        return 1 + len(self)

class Next(Term):
    """
    A next term is true if the O(e1) + 1 = O(e2)

    """
    
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def literals(self):
        yield from (self.e1, self.e2)
    
    @classmethod
    def from_values(cls, type_, e1, e2):
        lit = partial(Literal.literalize, type_)
        return cls(lit(e1), lit(e2))

    def size(self):
        return 3

class Boolean(Term):
    """
    Eighter True or False, depending on the value.
    """

    def __init__(self, value):
        self.value = value

    def literals(self):
        yield from []

    def size(self):
        return 1

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



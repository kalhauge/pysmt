"""
Logic
=====

.. currentmodule:: pysmt.logic

This file descripes the fundamental partial order logic, as used in this module.
"""

import itertools

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

    @staticmethod
    def literalize(value, type_):
        """
        Takes a value and makes it into a literal remembering the original
        value. If the value has a method called :meth:`rep`, this is called to
        generate the solution, else a name is generated from the hash value.
        """ 
        try: name = value.rep()
        except AttributeError: 
            name = 'l' + hash(value)

        return Literal(name, type_, value)


class Term:
    """ A piece of logic """

    @abstractmethod
    def literals(self):
        """ Returns the literals used in the term """

class All(Term):
    """ 
    All subterms must be true.
   
    .. attribute:: terms 
        
        The subterms that must be true. 
    """

    def __init__(self, terms):
        self.terms = list(terms) 

    def literals(self):
        yield from set(
            itertools.chain.from_iterable(
                term.literals() for term in self.terms
            )
        )

class Any(Term):
    """ 
    Any of the subterms must be true.
   
    .. attribute:: terms 
    
        The subterms that must be true. 
    """

    def __init__(self, terms):
        self.terms = list(terms)

    def literals(self):
        yield from set(
            itertools.chain.from_iterable(
                term.literals() for term in self.terms
            )
        )

class Order(Term):
    """ 
    All the literals must be ordered.
   
    .. attribute:: ordered_literals

        The literals must be ordered and givven values from small to large.
    """
    
    def __init__(self, literals):
        self.ordered_literals = list(literals)

    def literals(self):
        yield from self.ordered_literals

class Next(Term):
    """
    A next term is true if the O(e1) + 1 = O(e2)

    """
    
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

    def literals(self):
        yield from (self.e1, self.e2)




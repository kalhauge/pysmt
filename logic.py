"""
This file descripes the fundamental partial order logic, as used in this module.
"""

import itertools

from abc import abstractmethod
from collections import namedtuple

Literal = namedtuple('Literal', ['name', 'type'])

class Term:
    """ A piece of logic """

    @abstractmethod
    def literals(self):
        """ Returns the literals used in the term """

class All(Term):

    def __init__(self, terms):
        self.terms = list(terms) 

    def literals(self):
        yield from set(
            itertools.chain.from_iterable(
                term.literals() for term in self.terms
            )
        )

class Any(Term):

    def __init__(self, terms):
        self.terms = list(terms)

    def literals(self):
        yield from set(
            itertools.chain.from_iterable(
                term.literals() for term in self.terms
            )
        )

class Order(Term):
    
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




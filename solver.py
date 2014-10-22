"""
Solver
======

.. currentmodule:: pysmt.solver
.. moduleauthor:: Christian Kalhauge



"""
from abc import abstractmethod
import re
from subprocess import Popen, PIPE, STDOUT
import itertools
import time

import logging 
log = logging.getLogger('pysmt.solver')

from . import logic


class UnsatisfiableTerm (Exception): pass

class Solver:
    """
    The top level solver of all the logic in :mod:`pysmt.logic`. 
    """
   
    @abstractmethod 
    def satisfy(self, term):
        """ 
        Returns a dictionary of values satisfying the term ordered by
        the values of the literals, or an :class:`UnsatisfiableTerm` exception.
        """

class SMT2Solver (Solver):

    re_return = re.compile('(sat|unsat)')
    re_function = re.compile('\((?P<name>[^ \(\)]*) (?P<value>.*)\)')
    re_solution = re.compile(r'''
        \(
            ( \(
                [^\(\)]*
                ( 
                    \(- [^\(\)]*\) #Negative values
                    | [^\(\)]*
                ) 
            \) \s*)*
        \)
    ''', re.VERBOSE | re.MULTILINE)
    re_number = re.compile('(\(- (?P<minus>[0-9]+)\))|(?P<plus>[0-9]+)')
    
    def __init__(self, logic="QF_IDL"):
        self.logic = logic 
    
    def satisfiable(self, context, terms, solutions=False):
        """ For each term test if they are satitisfiable in the context of the
        world.
        """
        log.debug('Starting solveing terms using a context of size %s', context.size())
        literals = set(context.literals())
        with self.open():
            self.preable()
            self.declare_functions(literals)
            self.assert_term(context)
            for term in terms:
                log.debug('Solving Term of size %s.', term.size())
                term_literals = set(term.literals())
                self.send(['(push 1)'])
                self.declare_functions(term_literals - literals)
                self.assert_term(term)
                satisfied = self.has_solution()
                log.debug('Solution %s.', 'found' if satisfied else 'not found')
                if solutions:
                    if satisfied:
                        yield self.get_solution(literals | term_literals)
                    else:
                        yield None
                else:
                    yield satisfied
                self.send(['(pop 1)'])

    def satisfy(self, term):
        log.debug('Satisfing term of size %s', term.size())
        literals = set(term.literals())
        with self.open():
            self.preable()
            self.declare_functions(literals)
            self.assert_term(term)
            satisfied = self.has_solution()
            log.debug('Solution %s.', 'found' if satisfied else 'not found')
            if satisfied:
                return self.get_solution(literals)
            else:
                raise UnsatisfiableTerm()

    def filter(self, terms, context):
        test_terms, terms = itertools.tee(terms)
        tests = self.satisfiable(context, test_terms)
        return (term for term, test in zip(terms, tests) if test)

    def preable(self):
        self.send([
            '(set-option :produce-models true)',
            '(set-logic {})'.format(self.logic)
        ])
        
    def declare_functions(self, literals):
        self.send([
            '(declare-fun {0.name} () {0.type_})'.format(literal) 
            for literal in literals  # sorted(literals, key=lambda x:x.name)
        ])

    def assert_term(self, term):
        self.send([ '(assert {})'.format(self.compile(term)) ])

    def get_solution(self, literals):
        self.send([
            '(get-value ({}))'.format(
                ' '.join(literal.name for literal in literals)
        )])
        output = self.recv(self.re_solution)
        mapping = {}
        for match in self.re_function.finditer(output):
            value, name = match.group('value', 'name')
            if name == 'error':
                raise Exception(value)
            d = self.re_number.match(value).groupdict()
            value = -int(d['minus']) if d['minus'] else int(d['plus'])
            mapping[match.group('name')] = value

        solution = {}
        for literal in literals:
            solution[literal.value] = mapping[literal.name]

        return solution

    def compile(self, term, depth=0):
        indent = ('\n' + ' ' * (4 * (depth + 1)))
        if isinstance(term, logic.All):
            return '(and {})'.format(
                ''.join(
                    indent + self.compile(t, depth=depth+1) for t in term.terms
                ))
        elif isinstance(term, logic.Any):
            return '(or {})'.format(
                ''.join(
                    indent + self.compile(t, depth=depth+1) for t in term.terms
                ))
        elif isinstance(term, logic.Order):
            return '(< {})'.format(' '.join(l.name for l in term.literals()))
        elif isinstance(term, logic.Next):
            return '(= (+ {} 1) {})'.format(term.e1.name, term.e2.name)
        elif isinstance(term, logic.Boolean):
            return 'true' if term.value else 'false'
        elif isinstance(term, logic.Not):
            return '(not {})'.format(self.compile(term.subterm))
        elif isinstance(term, logic.Eq):
            return '(= {} {})'.format(term.e1.name, term.e2.name)
        else:
            raise NotImplementedError(
                "Don't know how to handle {}.".format(term)
            )


    def has_solution(self):
        self.send(['(check-sat)'])
        solution = self.recv(self.re_return)
        return solution == 'sat'

    def __enter__(self):
        if not self.is_open: 
            self.open()
        return self

    def __exit__(self, type, value, tb):
        self.close()

    @abstractmethod
    def send(self, command):
        """ Runs the commands and returns the output."""

    @abstractmethod
    def recv(self):
        """ Recieves a response """

    @abstractmethod
    def open(self):
        """ Opens up a connection to the solver, needs to return self""" 

    @abstractmethod
    def close(self):
        """ Closes the solver """

class Yices (SMT2Solver):

    def __init__(self, mode='QF_IDL'):
        self.process = None
        self.tempfile = None
        self.readbuffer = ''
        self.index = 0
        super().__init__(mode)

    def send(self, commands):
        for command in commands:
            print(command, file=self.tmpfile)
            print(command, file=self.process.stdin)
        self.process.stdin.flush()

    def recv(self, re=None):
        match = None
        counter = 0
        for line in self.process.stdout:
            self.readbuffer += line
            counter += line.count('(') - line.count(')')
            if counter <= 0:
                break        
             
            ## match = re.search(self.readbuffer, pos=self.index)
        match = self.readbuffer[self.index:]
        self.index = len(self.readbuffer) ## match.end(0)
        search = re.search(match).group(0)
        return search

    def open(self):
        self.index = 0
        self.readbuffer = ''
        filename, self.tmpfile = ensurefile()
        self.process = Popen(
            ['yices-smt2','--incremental'],
            universal_newlines=True,
            stdout=PIPE,
            stderr=STDOUT,
            stdin=PIPE,
        )
        return self

    def is_open(self):
        return not self.process is None

    def close(self):
        if self.is_open(): 
            self.process.stdin.close()
            self.process.terminate()
            self.tmpfile.close()
            self.process = None

def ensurefile(filename=None):
    if filename: 
        out = open(filename)
    else:
        import tempfile
        out = tempfile.NamedTemporaryFile("w+", suffix=".smt2", delete=False)
        filename = out.name
        log.debug("Generated temporary file %r", filename)
    return filename, out

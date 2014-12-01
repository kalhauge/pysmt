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

from .theories import core

DEBUG = False

class UnsatisfiableTerm (Exception): pass

class Solver:
    """
    """
   
    @abstractmethod 
    def satisfy(self, term):
        """ 
        Returns a dictionary of values satisfying the term ordered by
        the values of the symbols, or an :class:`UnsatisfiableTerm` exception.
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
    
    def __init__(self, logic="QF_IDL"):
        self.logic = logic 
    
    def satisfiable(self, context, terms, solutions=False):
        """ For each term test if they are satitisfiable in the context of the
        world.
        """
        log.debug('Starting solveing terms using a context of size %s', context.size())
        symbols = set(context.symbols())
        with self.open():
            self.preable()
            self.declare_functions(symbols)
            self.assert_term(context)
            for term in terms:
                log.debug('Solving Term of size %s.', term.size())
                term_symbols = set(term.symbols())
                self.send(['(push 1)'])
                self.declare_functions(term_symbols - symbols)
                self.assert_term(term)
                satisfied = self.has_solution()
                log.debug('Solution %s.', 'found' if satisfied else 'not found')
                if solutions:
                    if satisfied:
                        yield self.get_solution(symbols | term_symbols)
                    else:
                        yield None
                else:
                    yield satisfied
                self.send(['(pop 1)'])

    def satisfy(self, term):
        log.debug('Satisfing term of size %s', term.size())
        symbols = set(term.symbols())
        with self.open():
            self.preable()
            self.declare_functions(symbols)
            self.assert_term(term)
            satisfied = self.has_solution()
            log.debug('Solution %s.', 'found' if satisfied else 'not found')
            if satisfied:
                return self.get_solution(symbols)
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
        
    def declare_functions(self, symbols):
        self.send([
            '(declare-fun {0.name} () {0.type_.smt2})'.format(symbol) 
            for symbol in symbols  # sorted(symbols, key=lambda x:x.name)
        ])

    def assert_term(self, term):
        self.send([ '(assert {})'.format(self.compile(term)) ])

    def get_solution(self, symbols):
        if not symbols: return {}
        symbols_by_name = {s.name: s for s in symbols}
        self.send([
            '(get-value ({}))'.format(
                ' '.join(literal.name for literal in symbols)
        )])
        output = self.recv(self.re_solution)
        solution = {}
        for match in self.re_function.finditer(output):
            value, name = match.group('value', 'name')
            if name == 'error':
                raise Exception(value)
            symbol = symbols_by_name[name]
            if value.endswith(')') and not value.startswith('('):
               value = value[:-1]
            solution[symbol.value] = symbol.type_.parse_value(value)

        return solution

    def compile(self, term, depth=0):
        return term.compile_smt2()

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

class InteractiveSMT2Solver (SMT2Solver):

    def __init__(self, cmd, mode):
        self.process = None
        self.tempfile = None
        self.cmd = cmd
        self.readbuffer = ''
        self.index = 0
        super().__init__(mode)
    
    def send(self, commands):
        for command in commands:
            if DEBUG: print(command, file=self.tmpfile)
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
             
        match = self.readbuffer[self.index:]
        self.index = len(self.readbuffer) ## match.end(0)
        search = re.search(match).group(0)
        return search

    def open(self):
        self.index = 0
        self.readbuffer = ''
        if DEBUG: filename, self.tmpfile = ensurefile()
        self.process = Popen(
            self.cmd,
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
            if DEBUG: self.tmpfile.close()
            self.process = None


class Yices (InteractiveSMT2Solver):

    def __init__(self, mode='QF_IDL'):
        super().__init__(
            ['yices-smt2','--incremental'],
            mode)

class Boolector (InteractiveSMT2Solver):
    
    def __init__(self, mode='QF_NIA'):
        super().__init__(['boolector'], mode)



def ensurefile(filename=None):
    if filename: 
        out = open(filename)
    else:
        import tempfile
        out = tempfile.NamedTemporaryFile("w+", suffix=".smt2", delete=False)
        filename = out.name
        log.debug("Generated temporary file %r", filename)
    return filename, out

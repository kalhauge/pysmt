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

DEBUG = True

class UnsatisfiableTerm (Exception): pass

class SMT2Solver:
    """
    """
    def __init__(self, cmd, logic):
        self.cmd = cmd
        self.logic = logic
   
    @abstractmethod 
    def satisfy(self, term):
        """ 
        Returns a dictionary of values satisfying the term ordered by
        the values of the symbols, or an :class:`UnsatisfiableTerm` exception.
        """
        with self.client() as solver:
            solver.assert_(term)
            if solver.has_solution():
                return solver.get_solution()
            else:
                raise UnsatisfiableTerm('Term was not satisfiable')

    def satisfiable(self, terms, context=None, solutions=False):
        """
        Returns a list of eigther booleans, given the terms.
        """
        with self.client() as solver:
            if context is not None:
                solver.assert_(context)
            for term in terms:
                solver.push_context()
                solver.assert_(term)
                sat = solver.has_solution()
                if solutions: 
                    if sat: yield solver.get_solution()
                    else: yield None
                else:
                    yield sat
                solver.pop_context()

    def client(self):
        return SMT2SolverClient(self.cmd, self.logic)
    
    def filter(self, terms, context=None):
        test_terms, terms = itertools.tee(terms)
        tests = self.satisfiable(test_terms, context=context)
        return (term for term, test in zip(terms, tests) if test)

class Yices (SMT2Solver):

    def __init__(self, logic):
        cmd = ['yices-smt2','--incremental']
        super().__init__(cmd , logic)


class SolverClient:

    def __init__(self, cmd):
        self.process = None
        self.tempfile = None
        self.cmd = cmd
        self.readbuffer = ''
        self.index = 0
    
    def send(self, commands):
        for command in commands:
            if DEBUG: print(command, file=self.tmpfile)
            print(command, file=self.process.stdin)
        self.process.stdin.flush()

    def recv(self):
        """ Readlines until closing paranteses are read """
        counter = 0
        for line in self.process.stdout:
            self.readbuffer += line
            counter += line.count('(') - line.count(')')
            if counter <= 0:
                break        
             
        msg = self.readbuffer[self.index:]
        self.index = len(self.readbuffer)
        return msg

    def open(self):
        self.index = 0
        self.readbuffer = ''
        if DEBUG: filename, self.tmpfile = ensurefile()
        self.process = Popen(
            self.cmd, universal_newlines=True,
            stdout=PIPE, stderr=STDOUT, stdin=PIPE,
        )
        self.preamble()
        return self

    def close(self):
        self.process.stdin.close()
        self.process.terminate()
        if DEBUG: self.tmpfile.close()
        self.process = None

    def __enter__(self):
        if self.process is None:
            return self.open()
        else:
            raise ValueError('Running or a closed client')
        return self

    def __exit__(self, type, value, traceback):       
        self.close()


class SMT2SolverClient(SolverClient):

    def __init__(self, cmd, logic):
        super().__init__(cmd)
        self.logic = logic
        self.declared = set()
        self.symbols = set()
        self.stack = []

    def preamble(self):
        self.send([
            '(set-option :produce-models true)',
            '(set-logic {})'.format(self.logic)
        ])
        
    def assert_(self, term):
        symbols = term.symbols()
        operators = term.operators()
        
        decls = []
        defs = []
        
        for opr in operators:
            if opr in self.declared: continue
            self.declared.add(opr)
            
            decls.append(opr.declare())
            defs.append(opr.define())

        for sym in symbols:
            if sym in self.declared: continue
            self.declared.add(sym)
            
            decls.append(sym.declare())

        msg = decls + defs
        msg.append('(assert {})'.format(term.name))
        self.symbols |= symbols
        self.send(msg)

    def push_context(self):
        self.stack.append((set(self.declared), set(self.symbols)))
        self.send(['(push 1)'])

    def pop_context(self):
        self.declared, self.symbols = self.stack.pop()
        self.send(['(pop 1)'])

    re_return = re.compile('(sat|unsat)')

    def has_solution(self):
        self.send(['(check-sat)'])
        msg = self.recv()
        match = self.re_return.search(msg)
        if match is None:
            raise ValueError('Read strange msg: {!r}'.format(msg))
        else:
            return msg == 'sat\n'
    
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

    def get_solution(self):
        if not self.symbols: return {}
        symbols_by_name = {s.name: s for s in self.symbols}
        self.send(['(get-value ({}))'.format(' '.join(symbols_by_name))])
        output = self.recv()
        
        if self.re_solution.match(output) is None:
            raise ValueError('Read strange msg: {!r}'.format(msg))

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
     
def ensurefile(filename=None):
    if filename: 
        out = open(filename)
    else:
        import tempfile
        out = tempfile.NamedTemporaryFile("w+", suffix=".smt2", delete=False)
        filename = out.name
        log.debug("Generated temporary file %r", filename)
    return filename, out

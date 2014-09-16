"""
Solver
======

.. currentmodule:: pysmt.solver
.. moduleauthor:: Christian Kalhauge



"""
from abc import abstractmethod
import re

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
        the values of the litterals, or an :class:`UnsatisfiableTerm` exception.
        """

class SMT2Solver (Solver):

    re_return = re.compile('^(sat|unsat)$', re.MULTILINE)
    re_function = re.compile('\((?P<name>[^ \(\)]*) (?P<value>.*)\)')
    re_number = re.compile('(\(- (?P<minus>[0-9]+)\))|(?P<plus>[0-9]+)')

    def __init__(self, logic="QF_IDL"):
        self.count = 0
        self.logic = logic 
    
    def commands(self, term, literals=None): 
        if not literals:
            literals = list(term.literals())
        return [
            '(set-option :produce-models true)',
            '(set-logic {})'.format(self.logic)
        ] + [
            '(declare-fun {0.name} () {0.type_})'.format(literal) 
            for literal in literals 
        ] + [
            '(assert {})'.format(self.compile(term))
        ] + [ 
            '(check-sat)',
            '(get-value ({}))'.format(' '.join(
                literal.name for literal in literals 
            ))
        ]

    def compile(self, term, depth=0):
        self.count += 1
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
        else:
            raise NotImplementedError(
                "Don't know how to handle {}.".format(term)
            )

    def parse(self, output):
        mo = self.re_return.match(output)
        if mo is None:
            raise Exception('Bad compiling, {}'.format(output))
        elif mo.group(0) != 'sat':
            raise UnsatisfiableTerm(output)
    
        solution = {}
        for match in self.re_function.finditer(output):
            value = match.group('value')
            d = self.re_number.match(value).groupdict()
            value = -int(d['minus']) if d['minus'] else int(d['plus'])
            solution[match.group('name')] = value

        return solution
       
    def satisfy(self, term):
        log.debug('Satisfing term of size %s', term.size())
        commands = self.commands(term)
        self.count = 0
        output = self.run_commands(commands)
        try:
            mapping = self.parse(output)
            solution = {}
            for literal in term.literals():
                solution[literal.value] = mapping[literal.name]
            log.debug('Solution found, %s literals mapped', len(solution))
            return solution
        except UnsatisfiableTerm:
            log.debug('Solution NOT found')
            raise

    @abstractmethod
    def run_commands(self, term):
        """ Runs the commands and returns the output."""

class Yices (SMT2Solver):

    def run_commands(self, commands):
        from subprocess import check_output
        filename, out = ensurefile()
        with out:
            for command in commands:
                print(command, file=out)
        return check_output(
            ['yices-smt2', filename], 
            universal_newlines=True
        )

def ensurefile(filename=None):
    if filename: 
        out = open(filename)
    else:
        import tempfile
        out = tempfile.NamedTemporaryFile("w+", suffix=".smt2", delete=False)
        filename = out.name
        log.debug("Generated temporary file %r", filename)
    return filename, out


import re

from abc import abstractmethod
from . import logic

class UnsatisfiableTerm (Exception): pass

class Solver:
   
    @abstractmethod 
    def satisfy(self, term):
        """ Returns a dictionary with values satisfying the term or an
        UnsatisfiableTerm exception
        """

class SMT2Solver (Solver):

    re_sat = re.compile('^sat$', re.MULTILINE)
    re_function = re.compile('\((?P<name>[^ \(\)]*) (?P<value>.*)\)')
    re_number = re.compile('(\(- (?P<minus>[0-9]+)\))|(?P<plus>[0-9]+)')

    def __init__(self, logic="QF_IDL"):
        self.logic = logic 
    
    def commands(self, term, literals=None): 
        if not literals:
            literals = list(term.literals())
        return [
            '(set-option :produce-models true)',
            '(set-logic {})'.format(self.logic)
        ] + [
            '(declare-fun {0.name} () {0.type})'.format(literal) 
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
        else:
            raise NotImplementedError(
                "Don't know how to handle {}.".format(term)
            )

    def parse(self, output):
        if self.re_sat.match(output) is None:
             raise UnsatisfiableTerm("Order not satitsfiable")
    
        solution = {}
        for match in self.re_function.finditer(output):
            value = match.group('value')
            d = self.re_number.match(value).groupdict()
            value = -int(d['minus']) if d['minus'] else int(d['plus'])
            solution[match.group('name')] = value

        return solution
       
    def satisfy(self, term):
        commands = self.commands(term)
        output = self.run_commands(commands)
        return self.parse(output)

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
        print(filename)
    return filename, out

"""
Contains expressions and type bases
"""

from abc import abstractmethod

class Type:

    @abstractmethod
    def compile_smt2(self):
        """ Compiles itsself into a value """
        
    @abstractmethod
    def present_smt2(self, value):
        """ Persents a value in the right format """


def transverse(root):
    stack = [root]
    while stack:
        top = stack.pop()
        try:
            stack.extend(top.attributes())
        except AttributeError: pass
        yield top 


class Expression:
    """ A piece of artihmetic, can return anything. """

    def symbols(self):
        """ Returns the symbols used in the expression """
        symbols = set()
        for expr in self.subexpressions():
            if isinstance(expr, Symbol) and not expr in symbols:
                symbols.add(expr)
                yield expr

    def size(self):
        """ Returns the size of the expression, as in how many nodes in the
        experssion tree """
        return sum(1 for x in self.subexpressions())

    @abstractmethod
    def eval(self, inputs={}):
        """ Evaluates the expression """

    def iter_all(self):
        """ Iteratest though the entier tree in the samme order each time, in a
        depbth first mannor, only yielding all nodes and leafs """
        yield from transverse(self)

    def attributes(self):
        vs = vars(self)
        return (vs[x] for x in sorted(vs) if x[0] != '_')

    def subexpressions(self):
        yield from filter(lambda a: isinstance(a, Expression), self.iter_all())
    
    def subcontent(self):
        yield from filter(lambda a: not isinstance(a, Expression), self.iter_all())

    def __eq__(self, other):
        return (
            isinstance(other, Expression) and
            hash(self) == hash(other) and
            all(a == b for a, b in zip(self.subcontent(), other.subcontent()))
        )

    def simplify(self):
        return self

class Operator(Expression):
    """ An operator could be anything from a function, to a unaryoperater like
    not"""

    def __init__(self, *args):
        self._args = tuple(args)
        self._hash = hash(args)

    @property
    def args(self):
        return self._args

    def attributes(self):
        yield from super().attributes()
        yield from self._args 

    def eval(self, inputs={}):
        return self.opr(*[arg.eval(inputs) for arg in self.args])

    @classmethod
    def from_values(cls, *args):
        """ Method that indicates that free values might exist """ 
        return cls(*list(map(from_value, args)))

    def compile_smt2(self, mode, depth=0):
        sep = ' '
        if len(self.args) > 2: sep = '\n' + ' '*(4*(depth + 1))
        
        return '({}{})'.format(
            self.smt2_opr, 
            sep + sep.join(t.compile_smt2(mode, depth + 1) for t in self.args)
        )

    def __str__(self):
        return '({} {})'.format(
            self.smt2_opr, ' '.join(str(a) for a in self.args)
        )
    
    def __hash__(self):
        return self._hash


class BinaryOperator(Operator):
    """ A binary operator """
    
    def __init__(self, first, second):
        super().__init__(first, second)

    @property
    def first(self):
        return self.args[0]

    @property
    def second(self):
        return self.args[1]

class UnaryOperator(Operator):

    def __init__(self, value):
        super().__init__(value)

    @property
    def value(self):
        return self.args[0]

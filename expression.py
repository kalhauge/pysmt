"""
Contains expressions and type bases
"""

from abc import abstractmethod

def from_value(value):
    if isinstance(value, Expression):
        return value
    elif hasattr(value, 'symbol'):
        from pysmt.theories import ints
        return Symbol.from_value(ints.Int(), value)
    else:
        return Value.from_value(value)

class Type:

    @abstractmethod
    def compile_smt2(self):
        """ Compiles itsself into a value """

    smt2 = property(lambda self: self.compile_smt2()) 
        
    @abstractmethod
    def present_smt2(self, value):
        """ Persents a value in the right format """

    @abstractmethod
    def parse_value(self, string):
        """Parses a value"""
        raise NotImplementedError

    def get_value(self, value):
        return Value(self, value)

    def __repr__(self):
        return "<pysmt.Type: {}>".format(self.smt2)

class Expression:
    """ A piece of artihmetic, can return anything. """

    def __init__(self, name, type_):
        self.name = name
        self.type_ = type_
    
    @abstractmethod
    def eval(self, inputs={}):
        """ Evaluates the expression """
    
    @abstractmethod
    def simplify(self):
        """ Tries to reduce the expression """

    smt2 = property(lambda self: self.present())

    def symbols(self):
        """ Returns the symbols used in the expression """
        return set(expr for expr in self.transverse() 
            if isinstance(expr, Symbol))
    
    def operators(self):
        """ Returns the symbols used in the expression """
        return set(expr for expr in self.transverse() 
            if isinstance(expr, Operator))

    def size(self):
        """ Returns the size of the expression, as in how many nodes in the
        experssion tree """
        return sum(1 for x in self.transverse())

    def transverse(self):
        stack = [self]
        while stack:
            top = stack.pop()
            stack.extend(top.subexpressions)
            yield top 

    def __eq__(self, other):
        try:
            return ( 
                self.name == other.name and 
                self.type_ == other.type_
            )
        except AttributeError:
            return False

    def __hash__(self):
        return hash(self.name)


class Operator(Expression):
    """ 
    An operator could be anything from a function, to a unaryoperater like not
    
    All alike expressions have the same name, and can be compared on their name
    alone
    """

    ALL_OPR = {}
    
    next_name = 0

    @classmethod
    def uniq(cls, args):
        t = (cls, ) + args
        if not t in cls.ALL_OPR:
            cls.ALL_OPR[t] = cls(
                "expr_{}".format(Operator.next_name), 
                *args
            )
            Operator.next_name += 1
        return cls.ALL_OPR[t]

    def __init__(self, name, *args):
        assert isinstance(name, str)
        super().__init__(name, self.calculate_type(args))
        self._args = tuple(args)
    
    subexpressions = property(lambda self: self._args)

    @classmethod
    def calculate_type(cls, args):
        return cls.class_type 
    
    @classmethod
    def from_values(cls, *args):
        """ Method that indicates that free values might exist """ 
        args = tuple(map(from_value, args))
        return cls.uniq(args)
    
    def declare(self):
        return '(declare-fun {0.name} () {0.type_.smt2})'.format(self) 

    def define(self):
        return '(assert (= {0.name} {0.smt2}))'.format(self)

    @property
    def args(self):
        return self._args

    def eval(self, inputs={}):
        return self.opr(*[arg.eval(inputs) for arg in self.args])

    @property
    def smt2(self):
        return '({} {})'.format(
            self.smt2_opr, ' '.join(t.name for t in self.args)
        )

    def __str__(self):
        return '({} {})'.format(
            self.smt2_opr, ' '.join(str(a) for a in self.args)
        )

    def __repr__(self):
        return '<{}.{} {}>'.format(self.__module__, self.__class__.__name__, self._args)
    

class BinaryOperator(Operator):
    """ A binary operator """
    
    def __init__(self, name, first, second):
        super().__init__(name, first, second)

    first = property(lambda self: self.args[0])
    second = property(lambda self: self.args[0])

class UnaryOperator(Operator):

    def __init__(self, name, value):
        super().__init__(name, value)

    value = property(lambda self: self.args[0])

class Value(Expression):

    subexpressions = []

    def __init__(self, type_, value):
        super().__init__(type_.present_smt2(value), type_)
        self.value = value

    @classmethod 
    def from_value(cls, value):
        from .theories import ints, core
        lookup = {int: ints.Int, bool: core.Bool}
        try:
            return cls(lookup[type(value)](), value) 
        except KeyError:
            raise TypeError('{} not supported by pysmt.Value'.format(value))

    def eval(self, inputs={}):
        return self.value
   
    def __str__(self):
        return self.name

class Symbol(Expression):
    """
    A symbol is the values that we want to solve. The standart of this
    symbols are that they have to fulfill the SMTLIB specs, this means that the
    `name` and the `type_` must be according to thier specifications.

    :param str name: The name of the symbol
    :param str type_: The type of the symbol described by a string.
    :param value: The value that is symbol is associated with. This is
        used for traceability.
    """
    subexpressions = []

    def __init__(self, name, type_, value):
        super().__init__(name, type_)
        self.value = value

    @classmethod
    def from_value(cls, type_, value):
        """
        Takes a value and makes it into a literal remembering the original
        value. If the value has a attribute method called :meth:`symbol`, this is
        taken to generate the solution, else a name is generated from the hash
        value.
        """ 
        try:
            return cls(value.symbol, type_, value)
        except AttributeError:
            return cls('s' + str(hash(value)), type_, value)

    def eval(self, inputs={}):
        try: return inputs[self.name]
        except KeyError:
            return self.value

    def declare(self):
        return '(declare-fun {0.name} () {0.type_.smt2})'.format(self) 

    def __str__(self):
        return self.name

    def __repr__(self):
        return '<{}.{} {!r} {!r} {!r}>'.format(self.__module__, self.__class__.__name__, 
            self.name, self.type_, self.value
        )


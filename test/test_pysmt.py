import pysmt 

import pytest

import itertools

import logging

solver = pysmt.solver.Yices('QF_IDL')
logging.basicConfig(level=logging.DEBUG)

class Test():
    
    def __init__(self, id):
        self.id = id
   
    @property 
    def symbol(self):
        return 't' + str(self.id)

    def __repr__(self):
        return self.symbol

def test_yices_statisfy():
    t1, t2 = Test(0), Test(1)
    solution = solver.satisfy(pysmt.order(t1,t2))
    assert solution[t1] < solution[t2]
    
    solution = solver.satisfy(pysmt.order(t2,t1))
    assert solution[t2] < solution[t1]

def test_yices_statifiable():
    t1, t2, t3 = Test(1), Test(2), Test(3)
    context = pysmt.all([
        pysmt.order(t1, t3),
        pysmt.order(t2, t3),
    ])

    tests, other = itertools.tee(
        pysmt.order(a, b) for a, b in 
            itertools.permutations([t1, t2, t3], 2)
    )

    assert set( test for sat, test in 
        zip(solver.satisfiable(context, tests), other) if sat
    ) == set(pysmt.order(a, b) for a, b in [
        (t1, t3),
        (t2, t3),
        
        (t1, t2),
        (t2, t1),
    ])


def test_yices_filter():
    t1, t2, t3 = Test(1), Test(2), Test(3)
    context = pysmt.all([
        pysmt.order(t1, t3),
        pysmt.order(t2, t3),
    ])

    terms = (
        pysmt.order(a, b) for a, b in 
        itertools.permutations([t1, t2, t3], 2)
    )

    assert set(solver.filter(terms, context)) == set(pysmt.order(a, b) for a, b in [
        (t1, t3),
        (t2, t3),
        
        (t1, t2),
        (t2, t1),
    ])

TREES = {
    'simple' : pysmt.add(1, 3),
    'symbolic' : pysmt.Symbol('s1', 'Int', None),
    'combined' : pysmt.sub(pysmt.add(1, 4), pysmt.add(1, 1)), # (1 + 4) - 3
    'symbolic_combined' : pysmt.sub(
        pysmt.Symbol('s1', 'Int', None), 
        pysmt.add(1, 1),
    ), 
}

@pytest.fixture(params=TREES)
def tree_name(request):
    return request.param

@pytest.fixture
def tree(tree_name):
    return TREES[tree_name] 

def test_evaluation_tree(tree):
    assert isinstance(tree, pysmt.Expression)

def test_evaluation_inequality(tree):
    assert tree != pysmt.add(23, 42)

def test_evaluation_tree_evaulate(tree, tree_name):
    assert tree.eval({'s1':10, 's2':1}) == dict(
        simple=4,
        symbolic=10,
        combined=3,
        symbolic_combined=8,
    ).get(tree_name)

def test_evaluation_tree_evaulate_with_values(tree, tree_name):
    assert tree.eval({'s1':0, 's2':1}) == dict(
        simple=4,
        symbolic=0,
        combined=3,
        symbolic_combined=-2,
    ).get(tree_name)

def _test_evaluation_tree_reduce(tree, tree_name):
    assert tree.reduce() == dict(
        simple=C.Value(4),
        symbolic=C.Symbol(1, 10),
        combined=C.Value(3),
        symbolic_combined=C.SymbolicBinaryExpr(
            operator.sub, C.Symbol(1, 10), 2
        ),
        logic=C.SymbolicBinaryExpr(
            operator.lt,
            C.Symbol(1, 20),
            2
        ),
        symbolic_logic=C.SymbolicBinaryExpr(
            operator.lt, 
            C.Symbol(1, 10), 
            C.Symbol(2, -10), 
        ),
    ).get(tree_name)



@pytest.fixture(params=[
    ('#b00000', 0),
    ('#b10000', -16),
    ('#b00001', 1),
    ('#b11110', -2),
    ('#b10110', -10),
    ('#b00101', 5),
    ]
)
def bin5(request):
    return request.param

def test_bitvector_parse(bin5):
    from pysmt.theories import bitvectors
    type_ = bitvectors.BitVec(5)
    s, v = bin5
    assert type_.parse_value(s) == v

def test_bitvector_present_smt2(bin5):
    from pysmt.theories import bitvectors
    type_ = bitvectors.BitVec(5)
    s, v = bin5
    assert type_.present_smt2(v) == s

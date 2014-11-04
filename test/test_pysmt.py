import pysmt 
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
    solution = solver.satisfy(pysmt.logic.order(t1,t2))
    assert solution[t1] < solution[t2]
    
    solution = solver.satisfy(pysmt.logic.order(t2,t1))
    assert solution[t2] < solution[t1]

def test_yices_statifiable():
    t1, t2, t3 = Test(1), Test(2), Test(3)
    context = pysmt.all([
        pysmt.logic.order(t1, t3),
        pysmt.logic.order(t2, t3),
    ])

    tests, other = itertools.tee(
        pysmt.logic.order(a, b) for a, b in 
            itertools.permutations([t1, t2, t3], 2)
    )

    assert set( test for sat, test in 
        zip(solver.satisfiable(context, tests), other) if sat
    ) == set(pysmt.logic.order(a, b) for a, b in [
        (t1, t3),
        (t2, t3),
        
        (t1, t2),
        (t2, t1),
    ])


def test_yices_filter():
    t1, t2, t3 = Test(1), Test(2), Test(3)
    context = pysmt.all([
        pysmt.logic.order(t1, t3),
        pysmt.logic.order(t2, t3),
    ])

    terms = (
        pysmt.logic.order(a, b) for a, b in 
        itertools.permutations([t1, t2, t3], 2)
    )

    assert set(solver.filter(terms, context)) == set(pysmt.logic.order(a, b) for a, b in [
        (t1, t3),
        (t2, t3),
        
        (t1, t2),
        (t2, t1),
    ])

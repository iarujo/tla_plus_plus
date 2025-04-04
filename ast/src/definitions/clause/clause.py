"""

Elements for the AST representation of clauses or logical formulas.

"""

from typing import List, Union
from src.definitions.predicates.predicates import Predicate

class Clause:
    """
    An abstract TLA+ clause. 
    
    Definition sourced from Wikipedia, with my own modifications: 
    
    In logic, a clause is a propositional formula formed from a finite collection of literals (atoms or their negations) and logical connectives. 
    A clause is true either whenever at least one of the literals that form it is true (a disjunctive clause), or when all of the literals that 
    form it are true (a conjunctive clause). That is, it is a finite disjunction or conjunction of literals.
    
    """
    
    def __init__(self):
        pass
    
class Conjunction(Clause):
    
    """ A conjunction of literals """
    
    def __init__(self, literals: List[Union[Predicate, Clause]]):
        self.literals = literals
        
    def __repr__(self):
        return '(' + f"{' /\\ '.join(repr(l) for l in self.literals)})"    
    
class Disjunction(Clause):
    
    """ A disjunction of literals """
    
    def __init__(self, literals: List[Union[Predicate, Clause]]):
        self.literals = literals
        
    def __repr__(self):
        return ' (' + ' \\/ '.join(repr(l) for l in self.literals) + ')'
    
    
class Implication(Clause):
    
    """ An implication of two literals. Can also be written as ¬p ∨ q """
    
    def __init__(self, p: Union[Predicate, Clause], q: Union[Predicate, Clause]):
        self.p = p
        self.q = q
        
    def __repr__(self):
        return f"({self.p.__repr__()} => {self.q.__repr__()})"   
 
"""

Elements for the AST representation of clauses or logical formulas.

"""

from typing import List, Union
from src.definitions.predicates.predicates import Predicate
from copy import deepcopy

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
        if literals is None:
            raise ValueError("literals cannot be None")
        self.literals = literals
        
    def __repr__(self):
        lit = ["\n\t".join(repr(l).splitlines()) for l in self.literals]
        return '(' + ' /\\ '.join(lit) + ')'
    
    def getLiterals(self):
        """
        Returns the literals in the conjunction.
        """
        return deepcopy(self.literals)
    
    def add_literal(self, literal: Predicate):
        self.literals.append(literal)
        
    def remove_literal(self, literal: Predicate):
        """
        Removes a literal from the conjunction.
        """
        self.literals = [l for l in self.literals if l != literal]
        
    def get_node_count(self):
        """
        Returns the number of nodes in the clause.
        """
        count = 0
        for l in self.literals:
            count += l.get_node_count()
        return count
        
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        for l in self.literals:
            l.preCompile(spec)
    
    def compile(self, spec):
        """
        Compile this clause into a valid TLA+ specification.
        """
        return Conjunction(
            [l.compile(spec) for l in self.literals]
        )
        
    def byzComparisonToNormal(self, spec):
        """
        Convert Byzantine comparisons to normal comparisons.
        """
        return Conjunction(
            [l.byzComparisonToNormal(spec) for l in self.literals]
        )
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return any(l.isByzComparison() for l in self.literals)
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the clause to a new one.
        """
        for l in self.literals:
            l.changeAliasTo(old, new)
    
class Disjunction(Clause):
    
    """ A disjunction of literals """
    
    def __init__(self, literals: List[Union[Predicate, Clause]]):
        self.literals = literals
        
    def __repr__(self):
        lit = ["\n\t".join(repr(l).splitlines()) for l in self.literals]
        return '(' + " \\/ ".join(lit) + ')'
    
    def getLiterals(self):
        """
        Returns the literals in the conjunction.
        """
        return deepcopy(self.literals)
    
    def add_literal(self, literal: Predicate):
        self.literals.append(literal)
        
    def remove_literal(self, literal: Predicate):
        """
        Removes a literal from the disjunction.
        """
        self.literals = [l for l in self.literals if l != literal]
    
    def get_node_count(self):
        """
        Returns the number of nodes in the clause.
        """
        count = 0
        for l in self.literals:
            count += l.get_node_count()
        return count
        
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        for l in self.literals:
            l.preCompile(spec)
    
    def compile(self, spec):
        """
        Compile this clause into a valid TLA+ specification.
        """
        return Disjunction(
            [l.compile(spec) for l in self.literals]
        )
        
    def byzComparisonToNormal(self, spec):
        """
        Convert Byzantine comparisons to normal comparisons.
        """
        return Disjunction(
            [l.byzComparisonToNormal(spec) for l in self.literals]
        )
        
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return any(l.isByzComparison() for l in self.literals)
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the clause to a new one.
        """
        for l in self.literals:
            l.changeAliasTo(old, new)
    
class Implication(Clause):
    
    """ An implication of two literals. Can also be written as ¬p ∨ q """
    
    def __init__(self, p: Union[Predicate, Clause], q: Union[Predicate, Clause]):
        self.p = p
        self.q = q
        
    def __repr__(self):
        return f"({self.p.__repr__()} => {self.q.__repr__()})"  
    
    def  get_node_count(self):
        """
        Returns the number of nodes in the clause.
        """
        return self.p.get_node_count() + self.q.get_node_count() + 1
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.p.preCompile(spec)
        self.q.preCompile(spec)
    
    def compile(self, spec):
        """
        Compile this clause into a valid TLA+ specification.
        """
        return Implication(
            self.p.compile(spec), 
            self.q.compile(spec)
        ) 
        
    def byzComparisonToNormal(self, spec):
        """
        Convert Byzantine comparisons to normal comparisons.
        """
        return Implication(
            self.p.byzComparisonToNormal(spec), 
            self.q.byzComparisonToNormal(spec)
        ) 
        
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return self.p.isByzComparison() or self.q.isByzComparison()
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the clause to a new one.
        """
        self.p.changeAliasTo(old, new)
        self.q.changeAliasTo(old, new)
 
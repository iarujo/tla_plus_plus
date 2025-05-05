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
        lit = ["\n\t".join(repr(l).splitlines()) for l in self.literals]
        return '(' + ' /\\ '.join(lit) + ')'
    
    def add_literal(self, literal: Predicate):
        self.literals = self.literals.append(literal)
        
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
    
    def add_literal(self, literal: Predicate):
        self.literals = self.literals.append(literal)
        
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
 
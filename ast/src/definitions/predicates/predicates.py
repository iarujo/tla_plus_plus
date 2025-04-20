from typing import Union, List
from src.definitions.terms.term_abstract import AbstractTerm

class Predicate:
    """ 
    Receives non boolean function, constants, variables, etc. Returns boolean result 
    """
    
    def __init__(self):
        pass    
    
    
# Kind of weird to have TRUE and FALSE here, but will do for now
class TRUE:
    """
    Represents the TRUE constant in TLA+
    """
    def __init__(self):
        pass
    
    def __repr__(self):
        return "TRUE"
    
    def compile(self, spec):
        return TRUE()
    
class FALSE:
    """
    Represents the FALSE constant in TLA+
    """
    def __init__(self):
        pass
    
    def __repr__(self):
        return "FALSE"
    
    def compile(self, spec):
        return FALSE()

class UniversalQuantifier(Predicate):
    """
    Represents the universal quantifier \\A in TLA+
    """
    
    def __init__(self, variables: List[AbstractTerm], set: AbstractTerm, predicate: Predicate): # Note that quantifiers are the only predicates that can take other predicates as arguments
        self.variables = variables
        self.set = set
        self.predicate = predicate
        
    def __repr__(self):
        return f"\\A {', '.join(repr(v) for v in self.variables)} \\in  {repr(self.set)}: \n\t{"\t".join([f'{l}\n' for l in repr(self.predicate).splitlines()])}"

    def compile(self, spec):
        return UniversalQuantifier(
            variables=[v.compile(spec) for v in self.variables], 
            set=self.set.compile(spec), 
            predicate=self.predicate.compile(spec)
        )
        
class ExistentialQuantifier(Predicate):
    """
    Represents the existential quantifier \\E in TLA+
    
    """
    
    def __init__(self, variables: List[AbstractTerm], set: AbstractTerm, predicate: Predicate):
        self.variables = variables
        self.set = set
        self.predicate = predicate
        
    def __repr__(self):
        return f"\\E {', '.join(repr(v) for v in self.variables)} \\in {repr(self.set)}: \n\t{"\t".join([f'{l}\n' for l in repr(self.predicate).splitlines()])}"
    
    def compile(self, spec):
        return ExistentialQuantifier(
            variables=[v.compile(spec) for v in self.variables], 
            set=self.set.compile(spec), 
            predicate=self.predicate.compile(spec)
        )
  
class Not(Predicate):
    """
    Represents the negation of a predicate in TLA+
    """
    
    def __init__(self, predicate: Predicate):
        self.predicate = predicate
        
    def __repr__(self):
        return f"~({repr(self.predicate)})"  
    
    def compile(self, spec):
        return Not(self.predicate.compile(spec))
    
class In(Predicate):
    """ 
    Represents the set membership predicate \\in in TLA+
    """
    
    def __init__(self, left: AbstractTerm, right: AbstractTerm): # Note: left must be element of set, right must be set
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"{self.left} \\in {self.right}"
    
    def compile(self, spec):
        return In(self.left.compile(spec), self.right.compile(spec))
  
class SubsetEquals(Predicate):
    """
    Represents the subset equality predicate \\subseteq in TLA+
    """

    def __init__(self, left: AbstractTerm, right: AbstractTerm):
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"(({self.left}) \\subseteq ({self.right}))"
    
    def compile(self, spec):
        return SubsetEquals(self.left.compile(spec), self.right.compile(spec))
    
class ArithmeticComparison(Predicate):
    """
    Represents an comparison predicate in TLA+ that's meant to compare numbers
    """
    
    def __init__(self, left: AbstractTerm, right: AbstractTerm, symbol: str):
        self.left = left
        self.right = right
        self.symbol = symbol
        
    def __repr__(self):
        return f"(({self.left}) {self.symbol} ({self.right}))"
    
    def get_symbol(self):
        raise NotImplementedError("This method should be implemented in subclasses")
    
    def compile(self, spec):
        return ArithmeticComparison(
            left=self.left.compile(spec), 
            right=self.right.compile(spec), 
            symbol=self.symbol
        )
  
class Equals(ArithmeticComparison):
    
    def __init__(self, left: AbstractTerm, right: AbstractTerm):
        super().__init__(left, right, "=")
        
    def get_symbol(self):
        return "="
    
class NotEquals(ArithmeticComparison):
    
    def __init__(self, left: AbstractTerm, right: AbstractTerm):
        super().__init__(left, right, "#")
        
    def get_symbol(self):
        return "#"
    
class LessThan(ArithmeticComparison):
    
    def __init__(self, left: AbstractTerm, right: AbstractTerm):
        super().__init__(left, right, "<")
        
    def get_symbol(self):
        return "<"

class LessThanEquals(ArithmeticComparison):
    
    def __init__(self, left: AbstractTerm, right: AbstractTerm):
        super().__init__(left, right, "<=")
        
    def get_symbol(self):
        return "<="

class GreaterThan(ArithmeticComparison):
    
    def __init__(self, left: AbstractTerm, right: AbstractTerm):
        super().__init__(left, right, ">")
        
    def get_symbol(self):
        return ">"
        
class GreaterThanEquals(ArithmeticComparison):
    
    def __init__(self, left: AbstractTerm, right: AbstractTerm):
        super().__init__(left, right, ">=")
        
    def get_symbol(self):
        return ">="

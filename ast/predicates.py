from typing import Union, List
from term_abstract import AbstractTerm

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
    
class FALSE:
    """
    Represents the FALSE constant in TLA+
    """
    def __init__(self):
        pass
    
    def __repr__(self):
        return "FALSE"

class UniversalQuantifier(Predicate):
    """
    Represents the universal quantifier \\A in TLA+
    """
    
    def __init__(self, variables: List[AbstractTerm], set: AbstractTerm, predicate: Predicate): # Note that quantifiers are the only predicates that can take other predicates as arguments
        self.variables = variables
        self.set = set
        self.predicate = predicate
        
    def __repr__(self):
        return f"(\\A {', '.join(repr(v) for v in self.variables)} \\in  {repr(self.set)}: {repr(self.predicate)})"

class ExistentialQuantifier(Predicate):
    """
    Represents the existential quantifier \\E in TLA+
    
    """
    
    def __init__(self, variables: List[AbstractTerm], set: Union[AbstractTerm, AbstractTerm], predicate: Predicate):
        self.variables = variables
        self.set = set
        self.predicate = predicate
        
    def __repr__(self):
        return f"(\\E {', '.join(repr(v) for v in self.variables)} \\in  {repr(self.set)}: {repr(self.predicate)})"
  
class Not(Predicate):
    """
    Represents the negation of a predicate in TLA+
    """
    
    def __init__(self, predicate: Predicate):
        self.predicate = predicate
        
    def __repr__(self):
        return f"~({repr(self.predicate)})"  
    
class In(Predicate):
    """ 
    Represents the set membership predicate \\in in TLA+
    """
    
    def __init__(self, left: Union[AbstractTerm, AbstractTerm], right: Union[AbstractTerm, AbstractTerm]): # Note: left must be element of set, right must be set
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"{self.left} \\in {self.right}"
  
class SubsetEquals(Predicate):
    """
    Represents the subset equality predicate \\subseteq in TLA+
    """

    def __init__(self, left: Union[AbstractTerm, AbstractTerm], right: Union[AbstractTerm, AbstractTerm]):
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"(({self.left}) \\subseteq ({self.right}))"
  
class Equals(Predicate):
    
    def __init__(self, left: Union[AbstractTerm, AbstractTerm], right: Union[AbstractTerm, AbstractTerm]):
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"(({self.left}) = ({self.right}))"
    
class NotEquals(Predicate):
    
    def __init__(self, left: Union[AbstractTerm, AbstractTerm], right: Union[AbstractTerm, AbstractTerm]):
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"(({self.left}) # ({self.right}))"
    
class LessThan(Predicate):
    
    def __init__(self, left: Union[AbstractTerm, AbstractTerm], right: Union[AbstractTerm, AbstractTerm]):
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"(({self.left}) < ({self.right}))"

class LessThanEquals(Predicate):
    
    def __init__(self, left: Union[AbstractTerm, AbstractTerm], right: Union[AbstractTerm, AbstractTerm]):
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"(({self.left}) <= ({self.right}))"

class GreaterThan(Predicate):
    
    def __init__(self, left: Union[AbstractTerm, AbstractTerm], right: Union[AbstractTerm, AbstractTerm]):
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"(({self.left}) > ({self.right}))"
    
class GreaterThanEquals(Predicate):
    
    def __init__(self, left: Union[AbstractTerm, AbstractTerm], right: Union[AbstractTerm, AbstractTerm]):
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"(({self.left}) >= ({self.right}))"

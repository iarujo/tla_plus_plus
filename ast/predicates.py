from typing import Union
from term_abstract import AbstractTerm
from alias import Alias

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
    
    def __init__(self, variable: str, set: Union[AbstractTerm, Alias], predicate: Predicate): # Note that quantifiers are the only predicates that can take other predicates as arguments
        self.variable = variable
        self.set = set
        self.predicate = predicate
        
    def __repr__(self):
        return f"\\A {self.variable.__repr__()} \\in  {self.set.__repr__()}: {self.predicate.__repr__()}"

class ExistentialQuantifier(Predicate):
    
    def __init__(self, variable: str, set: Union[AbstractTerm, Alias], predicate: Predicate):
        self.variable = variable
        self.set = set
        self.predicate = predicate
        
    def __repr__(self):
        return f"\\E {self.variable.__repr__()} \\in  {self.set.__repr__()}: {self.predicate.__repr__()}"
  
class Not(Predicate):
    
    def __init__(self, predicate: Predicate):
        self.predicate = predicate
        
    def __repr__(self):
        return f"~{self.predicate.__repr__()}"  
  
class Equals(Predicate):
    
    def __init__(self, left: Union[AbstractTerm, Alias], right: Union[AbstractTerm, Alias]): # TODO: add types for left & right
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"{self.left} = {self.right}"
    
class NotEquals(Predicate):
    
    def __init__(self, left: Union[AbstractTerm, Alias], right: Union[AbstractTerm, Alias]):
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"{self.left} # {self.right}"
    
class LessThan(Predicate):
    
    def __init__(self, left: Union[AbstractTerm, Alias], right: Union[AbstractTerm, Alias]):
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"{self.left} < {self.right}"

class LessThanEquals(Predicate):
    
    def __init__(self, left: Union[AbstractTerm, Alias], right: Union[AbstractTerm, Alias]):
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"{self.left} <= {self.right}"

class GreaterThan(Predicate):
    
    def __init__(self, left: Union[AbstractTerm, Alias], right: Union[AbstractTerm, Alias]):
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"{self.left} > {self.right}"
    
class GreaterThanEquals(Predicate):
    
    def __init__(self, left: Union[AbstractTerm, Alias], right: Union[AbstractTerm, Alias]):
        self.left = left
        self.right = right
        
    def __repr__(self):
        return f"{self.left} >= {self.right}"

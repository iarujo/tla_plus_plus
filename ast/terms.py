from term_abstract import AbstractTerm
from predicates import Equals, NotEquals, LessThan, LessThanEquals, GreaterThan, GreaterThanEquals
from typing import List

class Term:

    """ Umbrella class for functions, variables, and constants. """

    def __init__(self):
        pass
    
    def __add__(self, other):
        return Addition(self, other)


    def __sub__(self, other):
        return Substraction(self, other)


    def __mul__(self, other):
        return Multiplication(self, other)
    
    def __truediv__(self, other):
        return Division(self, other)
    
    def __eq__(self, value):
        return Equals(self, value)
    
    
    def __ne__(self, value):
        return NotEquals(self, value)
    
    
    def __lt__(self, value):
        return LessThan(self, value)
    
    
    def __le__(self, value):
        return LessThanEquals(self, value)
    
    
    def __gt__(self, value):
        return GreaterThan(self, value)

    
    def __ge__(self, value):
        return GreaterThanEquals(self, value)


class Scalar(Term):
    """
    Term representing a scalar value (in mathemathical logic, this is also referred to as a constant). 
    """

    def __init__(
            self,
            value: int):
        
        super().__init__()
        self.value = value

    def __repr__(self):
        return f"{self.value}"
    
    
class Variable(Term):
    """
    Term representing a variable, as defined in the TLA+ spec under VARIABLES 
    """

    def __init__(
            self,
            name: str):
        
        super().__init__()
        self.name = name

    def __repr__(self):
        return f"{self.name}"
    
    
class Constant(Term):
    """
    Term representing a constant, as defined in the TLA+ spec under CONSTANTS 
    """

    def __init__(
            self,
            name: str):
        
        super().__init__()
        self.name = name

    def __repr__(self):
        return f"{self.name}"
    
class Record(Term):
    """
    Term representing a record that's being defined, with syntax [val1 : type1, val2 : type2, ...]
    """

    def __init__(
            self,
            vals: List[str],
            types: List[str]): # TODO: Should this be str or something else?
        
        super().__init__()
        self.vals = vals
        self.types = types

    def __repr__(self):
        return f"[{', '.join([f'{v} : {t}' for v, t in zip(self.vals, self.types)])}]"
    
class RecordInstance(Term):
    """
    Term representing an instance of a record, with syntax [val1 |-> value1, val2 |-> value2, ...]
    """

    def __init__(
            self,
            vals: List[str],
            types: List[Term]):
                
        super().__init__()
        self.vals = vals
        self.types = types

    def __repr__(self):
        return f"[{', '.join([f'{v} |-> {repr(t)}' for v, t in zip(self.vals, self.types)])}]"
    
    
class Function(Term):
    """
    Term taking one or more terms as arguments and returning another term.
    """
    
    def __init__(self):
        pass


class Union(Function):
    """ Intermediate AST nodes representing union """
    def __init__(
            self,
            a: Term,
            b: Term):
        
        super().__init__()
        self.a = a
        self.b = b

    def __repr__(self):
        return (
            f"{repr(self.a)} \\cup {repr(self.b)}"
        )
        
        
class Intersection(Function):
    """ Intermediate AST nodes representing intersection """
    def __init__(
            self,
            a: Term,
            b: Term):
        
        super().__init__()
        self.a = a
        self.b = b

    def __repr__(self):
        return (
            f"{repr(self.a)} \\cap {repr(self.b)}"
        )
        

class Addition(Function):
    """ Intermediate AST nodes representing addition """

    def __init__(
            self,
            a: Term,
            b: Term):
        
        super().__init__()
        self.a = a
        self.b = b

    def __repr__(self):
        return (
            f"({repr(self.a)} + {repr(self.b)})"
        )
        

class Substraction(Function):
    """ Intermediate AST nodes representing substraction """

    def __init__(
            self,
            a: Term,
            b: Term):
        
        super().__init__()
        self.a = a
        self.b = b

    def __repr__(self):
        return (
            f"({repr(self.a)} - {repr(self.b)})"
        )
        

class Multiplication(Function):
    """ Intermediate AST nodes representing multiplication """

    def __init__(
            self,
            a: Term,
            b: Term):
        
        super().__init__()
        self.a = a
        self.b = b

    def __repr__(self):
        return (
            f"{repr(self.a)} * {repr(self.b)}"
        )
        
class Division(Function):
    """ Intermediate AST nodes representing multiplication """

    def __init__(
            self,
            a: Term,
            b: Term):
        
        super().__init__()
        self.a = a
        self.b = b

    def __repr__(self):
        return (
            f"{repr(self.a)} \\div {repr(self.b)}"
        )

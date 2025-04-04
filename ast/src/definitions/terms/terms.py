from typing import List, Optional
from src.definitions.terms.term_abstract import AbstractTerm
from src.definitions.predicates.predicates import Equals, NotEquals, LessThan, LessThanEquals, GreaterThan, GreaterThanEquals

# TODO: Add subclasses in different files for simple terms, arithmetic operations, set operations, etc.

class Term(AbstractTerm):

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
    
    
    def __ge__(self, value):
        return LessThanEquals(value, self)
    
    
    def __gt__(self, value):
        return GreaterThan(self, value)

    
    def __le__(self, value):
        return GreaterThanEquals(value, self)


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
    
class String(Term):
    """
    Term representing a string value.
    """

    def __init__(
            self,
            value: str):
        
        super().__init__()
        self.value = value

    def __repr__(self):
        return f'"{self.value}"'

class Alias(Term):
    """Term representing an alias for a definition that must be declared elsewhere in the AST."""
    # Note: some aliases return boolean values, while others just return a value of any other kind. Should we make a distinction between these?

    def __init__(
            self,
            name: str,
            arguments: Optional[List[str]] = None):
        
        self.name = name
        if arguments is None:
            self.arguments = []
        else:
            self.arguments = arguments

    def __repr__(self):
        if(self.arguments):
            return f"{self.name}({', '.join(repr(a) for a in self.arguments)})"
        return f"{self.name}"
    
class Function(Term):
    """
    Term taking one or more terms as arguments and returning another term.
    """
    
    def __init__(self):
        pass
    
class Unchanged(Term):
    """
    Represents the unchanged operator in TLA+
    """
    
    def __init__(
            self,
            var: Term):
        
        super().__init__()
        self.var = var

    def __repr__(self):
        return f"UNCHANGED {repr(self.var)}"
    
class Choose(Term):
    """
    Represents the choose operator in TLA+
    """
    
    def __init__(
            self,
            var: Alias,
            set: Term,
            predicate: Term):
        
        super().__init__()
        self.var = var
        self.set = set
        self.predicate = predicate

    def __repr__(self):
        return f"CHOOSE {repr(self.var)} \\in {repr(self.set)}: {repr(self.predicate)}"
    
class Enabled(Term):
    """
    Represents the enable operator in TLA+
    """
    
    def __init__(
            self,
            var: Alias):
        
        super().__init__()
        self.var = var

    def __repr__(self):
        return f"ENABLED {repr(self.var)}"
    
class Range(Term):
    """
    Represents a range of values in TLA+.
    """

    def __init__(
            self,
            start: Term,
            end: Term):
        
        super().__init__()
        self.start = start
        self.end = end

    def __repr__(self):
        return f"{repr(self.start)}..{repr(self.end)}"
    
""" Arithmetic operations """

class BinaryArithmeticOp(Function):
    def __init__(self, a: Term, b: Term, symbol: str):
        super().__init__()
        self.a = a
        self.b = b
        self.symbol = symbol
        
    def __repr__(self):
        return f"({repr(self.a)} {self.symbol} {repr(self.b)})"


class Addition(BinaryArithmeticOp):
    """ Intermediate AST nodes representing addition """

    def __init__(
            self,
            a: Term,
            b: Term):
        
        super().__init__(a, b, "+")
        

class Substraction(BinaryArithmeticOp):
    """ Intermediate AST nodes representing substraction """

    def __init__(
            self,
            a: Term,
            b: Term):
        super().__init__(a, b, "-")

class Multiplication(BinaryArithmeticOp):
    """ Intermediate AST nodes representing multiplication """

    def __init__(
            self,
            a: Term,
            b: Term):
        
        super().__init__(a, b, "*")
        
class Division(BinaryArithmeticOp):
    """ Intermediate AST nodes representing multiplication """

    def __init__(
            self,
            a: Term,
            b: Term):
        
        super().__init__(a, b, " \\div")

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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        raise NotImplementedError("This method should be implemented in subclasses.")
    
    def compile(self, spec):
        """
        Transforms the term into a valid TLA+ term.
        """
        raise NotImplementedError("This method should be implemented in subclasses.")
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        pass
    


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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        pass
    
    def compile(self, spec):
        return self
    
    
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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        pass
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        pass
    
    def compile(self, spec):
        return self
    
    
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
    
    def get_name(self):
        """
        Returns the name of the constant.
        """
        return self.name
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        pass
    
    def compile(self, spec):
        return self
    
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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        pass
    
    def compile(self, spec):
        return self

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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        pass
    
    def compile(self, spec):
        return self
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        if self.name == old:
            self.name = new
        for i in range(len(self.arguments)):
            self.arguments[i].changeAliasTo(old, new)
    
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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.var.preCompile(spec)
    
    def compile(self, spec):
        return Unchanged(self.var.compile(spec))
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.var.changeAliasTo(old, new)
    
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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.var.preCompile(spec)
        self.set.preCompile(spec)
        self.predicate.preCompile(spec)
    
    def compile(self, spec):
        return Choose(self.var.compile(spec), self.set.compile(spec), self.predicate.compile(spec))
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.var.changeAliasTo(old, new)
        self.set.changeAliasTo(old, new)
        self.predicate.changeAliasTo(old, new)
    
    
    
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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.var.preCompile(spec)
    
    def compile(self, spec):
        return Enabled(self.var.compile(spec))
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.var.changeAliasTo(old, new)
    
    
    
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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.start.preCompile(spec)
        self.end.preCompile(spec)
    
    def compile(self, spec):
        return Range(self.start.compile(spec), self.end.compile(spec))
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.start.changeAliasTo(old, new)
        self.end.changeAliasTo(old, new)
    
    
    
""" Arithmetic operations """

class BinaryArithmeticOp(Function):
    def __init__(self, a: Term, b: Term, symbol: str):
        super().__init__()
        self.a = a
        self.b = b
        self.symbol = symbol
        
    def __repr__(self):
        return f"({repr(self.a)} {self.symbol} {repr(self.b)})"

    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.a.preCompile(spec)
        self.b.preCompile(spec)

    def compile(self, spec):
        return BinaryArithmeticOp(self.a.compile(spec), self.b.compile(spec), self.symbol)
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.a.changeAliasTo(old, new)
        self.b.changeAliasTo(old, new)
    

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

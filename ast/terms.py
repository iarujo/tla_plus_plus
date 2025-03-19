from term_abstract import AbstractTerm
from predicates import Equals, NotEquals, LessThan, LessThanEquals, GreaterThan, GreaterThanEquals
from typing import List, Optional

# TODO: Add subclasses in different files for simple terms, arithmetic operations, set operations, etc.

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
    
# TODO: The following classes need more refining in therms of what classes of elements they accept    
    
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
    
class Mapping(Term): 
    """
    Term representing a TLA+ function (mapping) ]
    """

    def __init__(
            self,
            vals: List[str],
            types: List[str]): # TODO: Records and Mappings still need a lot of work in terms of handling different input types
        
        super().__init__()
        self.vals = vals
        self.types = types

    def __repr__(self):
        return f"[{', '.join([f'{v} -> {t}' for v, t in zip(self.vals, self.types)])}]"
    
    
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
    
class IndexSet(Function):
    """
    Represents the indexing operation of a set
    """
    
    def __init__(
            self,
            set: Term,
            index: Term):
        
        super().__init__()
        self.set = set
        self.index = index

    def __repr__(self):
        return f"{repr(self.set)}[{repr(self.index)}]"
    
class Subset(Function):
    
    def __init__(
            self,
            set: Term):
        
        super().__init__()
        self.set = set

    def __repr__(self):
        return f"SUBSET {repr(self.set)}"
    
class Set(Function):
    """ Represents the empty set """
    
    def __init__(self, elems: List[Term]):
        super().__init__()
        self.elems = elems
    def __repr__(self):
        return "{" + f"{', '.join(repr(e) for e in self.elems)}" + "}"
    
class SetOf(Function):
    """ Operator to create a set of elements belonging to a certain subset that satisfy a certain predicate """
    
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
        return f"{{ {repr(self.var)} \\in {repr(self.set)}: {repr(self.predicate)} }}"
    
class SetExcept(Function):
    """ Operator to return a set with a certain entry changed. Syntax: [ set EXCEPT ![index] = value] """
    def __init__(
            self,
            set: Term,
            index: Term,
            value: Term):
        
        super().__init__()
        self.set = set
        self.index = index
        self.value = value
        
    def __repr__(self):
        return f"[{repr(self.set)} EXCEPT ![{repr(self.index)}] = {repr(self.value)}]"
    
class Cardinality(Function):
    
    def __init__(
            self,
            set: Term):
        
        super().__init__()
        self.set = set
    
    def __repr__(self):
        return f"Cardinality({repr(self.set)})"


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
            f"({repr(self.a)} \\cup {repr(self.b)})"
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
            f"({repr(self.a)} \\cap {repr(self.b)})"
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
            f"({repr(self.a)} * {repr(self.b)})"
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
            f"({repr(self.a)} \\div {repr(self.b)})"
        )

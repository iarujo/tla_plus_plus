from typing import List
from src.definitions.terms.terms import Term, Alias, Function

""" Set Operations """

class IndexSet(Function):
    """
    Represents the indexing operation of a set.
    Syntax: set[index]
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
    
    def compile(self, spec):
        """
        Compile the set operation into a valid TLA+ term.
        """
        return IndexSet(self.set.compile(spec), self.index.compile(spec))
    
class Subset(Function):
    """ Represents a subset of a set. 
        Syntax: SUBSET set
    """
    
    def __init__(
            self,
            set: Term):
        
        super().__init__()
        self.set = set

    def __repr__(self):
        return f"SUBSET {repr(self.set)}"
    
    def compile(self, spec):
        """
        Compile the subset operation into a valid TLA+ term.
        """
        return Subset(self.set.compile(spec))
    
class Set(Function):
    """ Represents a set of elements. 
        Syntax: { elem1, elem2, ... }
    """
    
    def __init__(self, elems: List[Term]):
        super().__init__()
        self.elems = elems
        
    def __repr__(self):
        return "{" + f"{', '.join(repr(e) for e in self.elems)}" + "}"
    
    def compile(self, spec):
        """
        Compile the set operation into a valid TLA+ term.
        """
        return Set([e.compile(spec) for e in self.elems])
    
class SetOf(Function):
    """ Operator to create a set of elements belonging to a certain subset that satisfy a certain predicate
        Syntax: { var \\in set: predicate }
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
        return f"{{ {repr(self.var)} \\in {repr(self.set)}: {repr(self.predicate)} }}"
    
    def compile(self, spec):
        """
        Compile the set operation into a valid TLA+ term.
        """
        return SetOf(self.var.compile(spec), self.set.compile(spec), self.predicate.compile(spec))
   
class SetFrom(Function):
    """ Set of elements fulfilling a certain condition
        Syntax: { var: predicate }
    """
    
    def __init__(
            self,
            var: Alias,
            predicate: Term):
        
        super().__init__()
        self.var = var
        self.predicate = predicate

    def __repr__(self):
        return f"{{ {repr(self.var)}: {repr(self.predicate)} }}"
    
    def compile(self, spec):
        """
        Compile the set operation into a valid TLA+ term.
        """
        return SetFrom(self.var.compile(spec), self.predicate.compile(spec))
    
    
class SetExcept(Function):
    """ Operator to return a set with a certain entry changed. 
        Syntax: [ set EXCEPT ![index] = value] 
    """
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
    
    def compile(self, spec):
        """
        Compile the set operation into a valid TLA+ term.
        """
        return SetExcept(self.set.compile(spec), self.index.compile(spec), self.value.compile(spec))
    
class Cardinality(Function):
    """ Returns the cardinality (number of elements) of a set.
        Syntax: Cardinality(set)
    """
    
    def __init__(
            self,
            set: Term):
        
        super().__init__()
        self.set = set
    
    def __repr__(self):
        return f"Cardinality({repr(self.set)})"
    
    def compile(self, spec):
        """
        Compile the cardinality operation into a valid TLA+ term.
        """
        return Cardinality(self.set.compile(spec))


class Union(Function):
    """ Returns the set resulting from the union of two sets.
        Syntax: set1 \\cup set2
    """
    
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
        
    def compile(self, spec):
        """
        Compile the union operation into a valid TLA+ term.
        """
        return Union(self.a.compile(spec), self.b.compile(spec))
        
        
class Intersection(Function):
    """ Returns the set resulting from the intersection of two sets.
        Syntax: set1 \\cap set2
    """
    
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
        
    def compile(self, spec):
        """
        Compile the intersection operation into a valid TLA+ term.
        """
        return Intersection(self.a.compile(spec), self.b.compile(spec))
        
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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.set.preCompile(spec)
        self.index.preCompile(spec)
    
    def compile(self, spec):
        """
        Compile the set operation into a valid TLA+ term.
        """
        return IndexSet(self.set.compile(spec), self.index.compile(spec))
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return self.set.isByzComparison() or self.index.isByzComparison()
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.set.changeAliasTo(old, new)
        self.index.changeAliasTo(old, new)
    
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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.set.preCompile(spec)
    
    def compile(self, spec):
        """
        Compile the subset operation into a valid TLA+ term.
        """
        return Subset(self.set.compile(spec))
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return self.set.isByzComparison()
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.set.changeAliasTo(old, new)
    
class Set(Function):
    """ Represents a set of elements. 
        Syntax: { elem1, elem2, ... }
    """
    
    def __init__(self, elems: List[Term]):
        super().__init__()
        self.elems = elems
        
    def __repr__(self):
        return "{" + f"{', '.join(repr(e) for e in self.elems)}" + "}"
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        for e in self.elems:
            e.preCompile(spec)
    
    def compile(self, spec):
        """
        Compile the set operation into a valid TLA+ term.
        """
        return Set([e.compile(spec) for e in self.elems])
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return any(e.isByzComparison() for e in self.elems)
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        for e in self.elems:
            e.changeAliasTo(old, new)
    
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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.var.preCompile(spec)
        self.set.preCompile(spec)
        self.predicate.preCompile(spec)
    
    def compile(self, spec):
        """
        Compile the set operation into a valid TLA+ term.
        """
        return SetOf(self.var.compile(spec), self.set.compile(spec), self.predicate.compile(spec))
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return self.set.isByzComparison() or self.predicate.isByzComparison()
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.var.changeAliasTo(old, new)
        self.set.changeAliasTo(old, new)
        self.predicate.changeAliasTo(old, new)
   
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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.var.preCompile(spec)
        self.predicate.preCompile(spec)
    
    def compile(self, spec):
        """
        Compile the set operation into a valid TLA+ term.
        """
        return SetFrom(self.var.compile(spec), self.predicate.compile(spec))
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return self.predicate.isByzComparison()
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.var.changeAliasTo(old, new)
        self.predicate.changeAliasTo(old, new)
    
    
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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.set.preCompile(spec)
        self.index.preCompile(spec)
        self.value.preCompile(spec)
    
    def compile(self, spec):
        """
        Compile the set operation into a valid TLA+ term.
        """
        return SetExcept(self.set.compile(spec), self.index.compile(spec), self.value.compile(spec))
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return self.set.isByzComparison() or self.index.isByzComparison() or self.value.isByzComparison()
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.set.changeAliasTo(old, new)
        self.index.changeAliasTo(old, new)
        self.value.changeAliasTo(old, new)
    
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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.set.preCompile(spec)
    
    def compile(self, spec):
        """
        Compile the cardinality operation into a valid TLA+ term.
        """
        return Cardinality(self.set.compile(spec))
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return self.set.isByzComparison()
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.set.changeAliasTo(old, new)


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
        
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.a.preCompile(spec)
        self.b.preCompile(spec)
        
    def compile(self, spec):
        """
        Compile the union operation into a valid TLA+ term.
        """
        return Union(self.a.compile(spec), self.b.compile(spec))
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return self.a.isByzComparison() or self.b.isByzComparison()
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.a.changeAliasTo(old, new)
        self.b.changeAliasTo(old, new)
        
        
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
        
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.a.preCompile(spec)
        self.b.preCompile(spec)
        
    def compile(self, spec):
        """
        Compile the intersection operation into a valid TLA+ term.
        """
        return Intersection(self.a.compile(spec), self.b.compile(spec))
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return self.a.isByzComparison() or self.b.isByzComparison()
        
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.a.changeAliasTo(old, new)
        self.b.changeAliasTo(old, new)
from typing import List
from src.definitions.terms.terms import Term

# TODO: The following classes need more refining in therms of what classes of elements they accept  
    
class Record(Term):
    """
    Term representing a record that's being defined.
    Syntax [val1 : type1, val2 : type2, ...]
    """

    def __init__(
            self,
            fields: List[str],
            types: List[Term]):
        
        super().__init__()
        if len(fields) != len(types):
            raise ValueError("You must assign a type to each value in the record input.")
        self.fields = fields
        self.types = types

    def __repr__(self):
        return f"[{', '.join([f'{f} : {repr(t)}' for f, t in zip(self.fields, self.types)])}]"
    
    def get_node_count(self):
        """
        Returns the number of nodes in the term.
        """
        return 1 + sum(t.get_node_count() for t in self.types)
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        for t in self.types:
            t.preCompile(spec)
    
    def compile(self, spec):
        """
        Compile this record into a valid TLA+ record.
        """
        return Record(self.fields, [t.compile(spec) for t in self.types])
    
    def byzComparisonToNormal(self, spec):
        """
        Compile this record into a valid TLA+ record.
        """
        return Record(self.fields, [t.byzComparisonToNormal(spec) for t in self.types])
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return any(t.isByzComparison() for t in self.types)
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        for t in self.types:
            t.changeAliasTo(old, new)
    
class RecordInstance(Term):
    """
    Term representing an instance of a record.
    Syntax [val1 |-> value1, val2 |-> value2, ...]
    """
    
    def __init__(
            self,
            fields: List[str],
            vals: List[Term]):
                
        super().__init__()
        if len(fields) != len(vals):
            raise ValueError("You must assign a value to each field in the record instance.")
        self.fields = fields
        self.vals = vals

    def __repr__(self):
        return f"[{', '.join([f'{f} |-> {repr(v)}' for f, v in zip(self.fields, self.vals)])}]"
    
    def get_node_count(self):
        """
        Returns the number of nodes in the term.
        """
        return 1 + sum(v.get_node_count() for v in self.vals)
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        for v in self.vals:
            v.preCompile(spec)
    
    def compile(self, spec):
        """
        Compile this record instance into a valid TLA+ record instance.
        """
        return RecordInstance(self.fields, [v.compile(spec) for v in self.vals])
    
    def byzComparisonToNormal(self, spec):
        """
        Compile this record instance into a valid TLA+ record instance.
        """
        return RecordInstance(self.fields, [v.byzComparisonToNormal(spec) for v in self.vals])
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return any(v.isByzComparison() for v in self.vals)
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        for v in self.vals:
            v.changeAliasTo(old, new)
    
class Mapping(Term): 
    """
    Term representing a TLA+ function (mapping)
    Syntax: [val1 -> type1, val2 -> type2, ...]
    """

    def __init__(
            self,
            vals: List[Term],
            funs: List[Term]):
        
        super().__init__()
        if len(vals) != len(funs):
            raise ValueError("You must assign an image to each input value in the mapping input.")
        self.vals = vals
        self.funs = funs

    def __repr__(self):
        return f"[{', '.join([f'{repr(v)} -> {repr(f)}' for v, f in zip(self.vals, self.funs)])}]"
    
    def get_node_count(self):
        """
        Returns the number of nodes in the term.
        """
        return 1 + sum(v.get_node_count() for v in self.vals) + sum(f.get_node_count() for f in self.funs)

    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        for v in self.vals:
            v.preCompile(spec)
        for f in self.funs:
            f.preCompile(spec)

    def compile(self, spec):
        """
        Compile this mapping into a valid TLA+ mapping.
        """
        return Mapping([v.compile(spec) for v in self.vals], [f.compile(spec) for f in self.funs])
    
    def byzComparisonToNormal(self, spec):
        """
        Compile this mapping into a valid TLA+ mapping.
        """
        return Mapping([v.byzComparisonToNormal(spec) for v in self.vals], [f.byzComparisonToNormal(spec) for f in self.funs])
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return any(v.isByzComparison() for v in self.vals) or any(f.isByzComparison() for f in self.funs)
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        for v in self.vals:
            v.changeAliasTo(old, new)
        for f in self.funs:
            f.changeAliasTo(old, new)
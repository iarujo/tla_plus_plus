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

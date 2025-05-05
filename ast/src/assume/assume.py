from typing import Union, Optional, List
from src.definitions.clause.clause import Clause
from src.definitions.predicates.predicates import Predicate
from src.definitions.terms.terms import Term

class Assume:
    
    def __init__(self, name: str, expr: Union[Clause, Predicate]):
        self.name = name
        self.expr = expr
        
    def __repr__(self):
        return f"ASSUME {self.name} == {self.expr.__repr__()}"
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.expr.preCompile(spec)
    
    def compile(self, spec):
        """
        Transforms the definition into a valid TLA+ definition.
        """
        return Assume(
            name=self.name,
            expr=self.expr.compile(spec)
        )
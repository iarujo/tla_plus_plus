from typing import Union
from src.definitions.clause.clause import Clause
from src.definitions.predicates.predicates import Predicate
from src.definitions.terms.terms import Term

class Assume:
    
    def __init__(self, name: str, expr: Union[Clause, Predicate]):
        self.name = name
        self.expr = expr
        
    def __repr__(self):
        return f"ASSUME {self.name} == {self.expr.__repr__()}"
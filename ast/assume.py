from typing import Union
from clause import Clause
from predicates import Predicate

class Assume:
    
    def __init__(self, name: str, expr: Union[Clause, Predicate]):
        self.name = name
        self.expr = expr
        
    def __repr__(self):
        return f"ASSUME {self.name} == {self.expr.__repr__()}"
from typing import List, Optional, Union
from clause import Clause
from predicates import Predicate

class Definition():
    
    def __init__(self, name: str,
                value: Union[Clause, Predicate],
                arguments: Optional[List[str]] = None):
        self.name = name
        self.value = value
        self.arguments = arguments

    def __repr__(self):
        if(self.arguments):
            return f"{self.name}({', '.join(repr(a) for a in self.arguments)}) == {self.value.__repr__()}"
        return f"{self.name} == {self.value.__repr__()}"
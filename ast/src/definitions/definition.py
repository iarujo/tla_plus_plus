from typing import List, Optional, Union
from src.definitions.clause.clause import Clause
from src.definitions.predicates.predicates import Predicate
from src.definitions.terms.terms import Term

class Definition():
    
    def __init__(self, name: str,
                value: Union[Clause, Predicate, Term],
                arguments: Optional[List[str]] = None):
        self.name = name
        self.value = value
        self.arguments = arguments

    def __repr__(self):
        if(self.arguments):
            return f"{self.name}({', '.join(repr(a) for a in self.arguments)}) == {self.value.__repr__()}"
        return f"{self.name} == {self.value.__repr__()}"
    
    def compile(self, spec):
        """
        Transforms the definition into a valid TLA+ definition.
        """
        return Definition(
            name=self.name,
            value=self.value.compile(spec),
            arguments=self.arguments
        )
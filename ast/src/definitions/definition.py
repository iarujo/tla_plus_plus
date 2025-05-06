from typing import List, Optional, Union
from src.definitions.clause.clause import Clause
from src.definitions.predicates.predicates import Predicate
from src.definitions.terms.terms import Term
import copy

class Definition():
    
    def __init__(self, name: str,
                value: Union[Clause, Predicate, Term],
                arguments: Optional[List[str]] = []):
        self.name = name
        self.value = value
        self.arguments = arguments
        
    def get_name(self):
        """
        Returns the name of the definition.
        """
        return self.name
    
    def with_set_name(self, new_name: str):
        """
        Returns the same definition with a different name.
        """
        return Definition(
            name=new_name,
            value=copy.deepcopy(self.value),
            arguments=copy.deepcopy(self.arguments)
        )
    
    def set_value(self, value: Union[Clause, Predicate, Term]):
        """
        Sets the value of the definition.
        """
        self.value = value

    def __repr__(self):
        if(self.arguments):
            return f"{self.name}({', '.join(repr(a) for a in self.arguments)}) == {self.value.__repr__()}"
        return f"{self.name} == {self.value.__repr__()}"
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.value.preCompile(spec)
    
    def compile(self, spec):
        """
        Transforms the definition into a valid TLA+ definition.
        """
        return Definition(
            name=self.name,
            value=self.value.compile(spec),
            arguments=self.arguments
        )
        
    def byzComparisonToNormal(self, spec):
        """
        Transforms the definition into a valid TLA+ definition.
        """
        return Definition(
            name=self.name,
            value=self.value.byzComparisonToNormal(spec),
            arguments=self.arguments
        )
        
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the predicate to a new one.
        """
        self.value.changeAliasTo(old, new)
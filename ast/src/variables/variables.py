
from typing import List
from src.definitions.terms.terms import Variable

class Variables():
    """ A collection of the program's variables """
    
    def __init__(self, variables: List[Variable]):
        self.variables = variables

    def __repr__(self):
        return f"VARIABLES {', '.join(v.__repr__() for v in self.variables)}"
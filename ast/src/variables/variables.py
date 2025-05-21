
from typing import List
from src.definitions.terms.terms import Variable
from copy import deepcopy

class Variables():
    """ A collection of the program's variables """
    
    def __init__(self, variables: List[Variable]):
        self.variables = variables
        
    def get_variables(self):
        """ Returns the list of variables """
        return deepcopy(self.variables)

    def __repr__(self):
        return f"VARIABLES {', '.join(v.__repr__() for v in self.variables)}"
    
    def get_node_count(self):
        """
        Returns the number of nodes
        """
        count = 1
        for v in self.variables:
            count += 1
        return count
        
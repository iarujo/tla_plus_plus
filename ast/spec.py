"""
This module contains the Spec class, which is used to represent a TLA+ specification.

Note that the validity of the produced TLA+ depends on the correctness of the tree (specially when using aliases)

"""

from typing import List, Optional
from definition import Definition
from constants import Constants
from assume import Assume
from variables import Variables

class Spec:
    
    def __init__(self, module: str, extends: List[str], constants: Constants, assumptions: Optional[Assume], variables: Variables, defs: List[Definition]):
        self.module = module
        self.extends = extends
        self.constants = constants
        self.assumptions = assumptions
        self.variables = variables
        self.defs = defs
        # TODO Add assumptions, theorems, and properties
    
    def __repr__(self):
        spec = f"------------------------ MODULE {self.module} ------------------------\n"
        spec += "EXTENDS " + ", ".join(self.extends) + "\n"
        spec += repr(self.constants) + "\n"
        spec += '' if self.assumptions is None else repr(self.assumptions) + "\n\n"
        spec += repr(self.variables) + "\n\n"
        spec += "\n\n".join([repr(d) for d in self.defs]) + "\n"
        spec += "\n============================================================================="
        return spec
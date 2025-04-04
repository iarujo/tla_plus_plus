"""
This module contains the Spec class, which is used to represent a TLA+ specification.

Note that the validity of the produced TLA+ depends on the correctness of the tree (specially when using aliases)

"""

from typing import List, Optional
from src.definitions.definition import Definition
from src.constants.constants import Constants
from src.assume.assume import Assume
from src.variables.variables import Variables

class Spec:
    
    def __init__(self, module: str, extends: List[str], constants: Constants, assumptions: Optional[Assume], variables: Variables, defs: List[Definition]):
        self.module = module # The name of the module
        self.extends = extends # The modules this module extends
        self.constants = constants # The constants of the module
        self.assumptions = assumptions # The assumptions of the module
        self.variables = variables # The variables of the module
        self.defs = defs # The definitions of the module
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
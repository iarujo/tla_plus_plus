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
        spec += '' if self.constants is None else repr(self.constants) + "\n"
        spec += '' if self.assumptions is None else repr(self.assumptions) + "\n\n"
        spec += '' if self.variables is None else repr(self.variables) + "\n\n"
        spec += '' if self.defs is None else "\n\n".join([repr(d) for d in self.defs]) + "\n"
        spec += "\n============================================================================="
        return spec
    
    def get_constants(self):
        """
        Returns the constants of the module.
        """
        return self.constants.constants
    
    def compile(self):
        """
        Compile this spec into a valid TLA+ specification.
        """
        return Spec(self.module, self.extends, self.constants, None if self.assumptions is None else [a.compile(self) for a in self.assumptions], self.variables, None if self.defs is None else [d.compile(self) for d in self.defs])


        
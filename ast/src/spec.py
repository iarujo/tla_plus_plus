"""
This module contains the Spec class, which is used to represent a TLA+ specification.

Note that the validity of the produced TLA+ depends on the correctness of the tree (specially when using aliases)

"""

from typing import List, Optional, Union
from src.definitions.definition import Definition
from src.definitions.clause.clause import Clause, Conjunction, Disjunction
from src.definitions.predicates.predicates import Predicate
from src.constants.constants import Constants
from src.assume.assume import Assume
from src.variables.variables import Variables

class Spec:
    
    def __init__(self, module: str, extends: List[str], constants: Constants, assumptions: Optional[List[Assume]], variables: Variables, defs: List[Definition]):
        self.module = module # The name of the module
        self.extends = extends # The modules this module extends
        self.constants = constants # The constants of the module
        self.assumptions = assumptions # The assumptions of the module
        self.variables = variables # The variables of the module
        self.defs = defs # The definitions of the module
        # TODO Add assumptions, theorems, and properties
    
    def __repr__(self):
        spec = f"------------------------ MODULE {self.module} ------------------------\n"
        spec += '' if self.constants is None else "EXTENDS " + ", ".join(self.extends) + "\n"
        spec += '' if self.constants is None else repr(self.constants) + "\n"
        spec += '' if self.assumptions is None else "\n\n".join([repr(a) for a in self.assumptions]) + "\n\n"
        spec += ('' if self.variables is None else repr(self.variables)) + "\n\n"
        spec += '' if self.defs is None else "\n\n".join([repr(d) for d in self.defs]) + "\n"
        spec += "\n============================================================================="
        return spec
    
    def get_constants(self):
        """
        Returns the constants of the module.
        """
        return self.constants.constants
    
    def get_variables(self):
        """
        Returns the variables of the module.
        """
        return self.variables.variables
    
    def prepend_to_defs(self, definition: Definition):
        if self.defs is None:
            self.defs = [definition]
        else:
            self.defs = [definition] + self.defs
        
    def compile(self):
        """
        Compile this spec into a valid TLA+ specification.
        """
        compiled_spec = Spec(self.module, self.extends, self.constants, None if self.assumptions is None else [], self.variables, None if self.defs is None else [])
        # We compile the assumptions and defts with the new spec so they can append any neccessary definitions. This also means that definitions and assumptions are not able to see other definitions nor assumptions
        if not self.assumptions is None:
            new_assumptions = [a.compile(compiled_spec) for a in self.assumptions]
            for a in new_assumptions:
                compiled_spec.assumptions.append(a)
        if not self.defs is None:
            new_defs = [d.compile(compiled_spec) for d in self.defs]
            for d in new_defs:
                compiled_spec.defs.append(d)
        return compiled_spec

        
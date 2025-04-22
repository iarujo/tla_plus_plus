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
        self.pending_updates = [] # The pending updates of the module for compilaation
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
        return None if self.constants is None else self.constants.constants
    
    def get_variables(self):
        """
        Returns the variables of the module.
        """
        return None if self.variables is None else self.variables.variables
    
    def get_init(self):
        for d in self.defs:
            if d.get_name() == "Init":
                return d
        return None
    
    def update_later(self, update: Definition):
        """
        Adds an update to the list of pending updates. For now, updates are just new versions of definitions that we will change in the spec
        """
        self.pending_updates.append(update)
        
    def update(self):
        """
        Updates the spec with the pending updates.
        """
        for update in self.pending_updates:
            for i, d in enumerate(self.defs):
                if d.get_name() == update.get_name():
                    self.defs[i] = update
                    break
        self.pending_updates = []
    
    def prepend_to_defs(self, definition: Definition):
        if self.defs is None:
            self.defs = [definition]
        else:
            # Check if the definition already exists in the list
            in_list = False
            for i, d in enumerate(self.defs):
                if d.get_name() == definition.get_name():
                    in_list = True
                    self.defs[i] = definition
                    return
            if not in_list:
                self.defs.insert(0, definition)
                
    def compile(self):
        """
        Compile this spec into a valid TLA+ specification.
        """
        compiled_spec = Spec(self.module, self.extends, self.constants, None if self.assumptions is None else [], self.variables, None if self.defs is None else  self.defs)
        # We compile the assumptions and defts with the new spec so they can append any neccessary definitions. This also means that definitions and assumptions are not able to see other definitions nor assumptions
        if not self.assumptions is None:
            new_assumptions = [a.compile(compiled_spec) for a in self.assumptions]
            for a in new_assumptions:
                compiled_spec.assumptions.append(a)
        if not self.defs is None:
            new_defs = [d.compile(compiled_spec) for d in self.defs]
            compiled_spec.defs = []
            for d in new_defs:
                compiled_spec.defs.append(d)
            compiled_spec.update()
        return compiled_spec

        
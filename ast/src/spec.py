"""
This module contains the Spec class, which is used to represent a TLA+ specification.

Note that the validity of the produced TLA+ depends on the correctness of the tree (specially when using aliases)

"""

from rich.console import Console
from rich.text import Text
from typing import List, Optional, Union
from src.definitions.definition import Definition
from src.definitions.clause.clause import Clause, Conjunction, Disjunction
from src.definitions.predicates.predicates import Predicate, In
from src.constants.constants import Constants
from src.definitions.terms.terms import Variable, Alias
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
    
    def get_definitions(self):
        """
        Returns the definitions of the module.
        """
        return None if self.defs is None else self.defs
    
    def get_init(self):
        for d in self.defs:
            if d.get_name() == "Init":
                return d
        return None
    
    def get_typeok(self):
        """
        Returns the TypeOK definition for the module.
        """
        for d in self.defs:
            if d.get_name() == "TypeOK":
                return d
        return None
    
    def get_typeok_of(self, var: Variable):
        """ Returns the TypeOK definition for a variable, as long as it is of the form VARIABLE \\in SET """
        for d in self.defs:
            if d.get_name() == f"{repr(var)}TypeOK" and isinstance(d, Definition) and isinstance(d.value, In):
                return d.value.right
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
            self.prepend_to_defs(update)
        self.pending_updates = []
        
    def update(self, update: Definition):
        """
        Updates the spec with the update.
        """
        self.prepend_to_defs(update)
    
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
                
    def precompilationSplitNextFairness(self, traces: List[List[str]]):
        """
        Splits the Next definition into two definitions: Next_Fair and Next_Unfair. This is done to enforce the right properties when compile Byzantine Comparisons.
        """
        
        def splitFairnessTrace(trace: List[str]):
            """
            Splits a trace into two traces: one for the fair transitions and one for the unfair transitions.
            """
            defFair = None
            defUnfair = None            
            
            # See if the definition at the head of the trace has been split yet
            notSplit = False
            hasFair = False
            hasUnfair = False
            for d in self.defs:
                if d.get_name() == trace[-1]:
                    notSplit = True
                    defFair = d
                if d.get_name() == trace[-1] + "_Fair":
                    hasFair = True
                    defFair = d
                if d.get_name() == trace[-1] + "_Unfair":
                    hasUnfair = True
                    defUnfair = d
            
            if notSplit:
            
                if (hasFair or hasUnfair):
                    raise Exception(f"Trace spec is not valid, as it contains the definitions {trace[-1]} and {trace[-1]}_Fair or {trace[-1]}_Unfair at the same time")
                
                # If it hasn't been split, split it
                index = next((i for i, d in enumerate(self.defs) if d.get_name() == trace[-1]), None)
                if index is None:
                    raise Exception(f"Definition with name {trace[-1]} not found in self.defs")
                self.defs = [x for x in self.defs if x.get_name() != trace[-1]]
                
                defFair = defFair.with_set_name(trace[-1] + "_Fair")
                defUnfair = defFair.with_set_name(trace[-1] + "_Unfair")
                
                 # If we're dealing with Next, add another definition for the conjunction of the fair and unfair versions
                if trace[-1] == "Next":
                    defNext = Definition("Next", Disjunction([Alias(trace[-1] + "_Fair", None), Alias(trace[-1] + "_Unfair", None)]))
                    self.defs.insert(index, defNext)
                    
                # Insert the definitions into the functions
                self.defs.insert(index, defUnfair)
                self.defs.insert(index, defFair)
                
                
        
            # If this definition calls yet another definition, make sure each of the fair/unfair functions call the right definition, then recurse
            if len(trace) > 1:
                defFair.changeAliasTo(trace[-2], f'{trace[-2]}_Fair')
                defUnfair.changeAliasTo(trace[-2], f'{trace[-2]}_Unfair')
                # Recursion
                splitFairnessTrace(trace[:-1])
            
            else:
                pass
            # Otherwise, make sure to place the regular comparison and byzantine comparison correctly
            
        
        for trace in traces:
            splitFairnessTrace(trace)
            
        # Now we need to update the assumptions to use the new definitions
            
            
        
                
                
    def compile(self):
        """
        Compile this spec into a valid TLA+ specification.
        """     
        console = Console()

        console.rule("[bold blue]🛠️ Compiler Initialized")
        
        compiled_spec = Spec(self.module, self.extends, self.constants, None if self.assumptions is None else [], self.variables, None if self.defs is None else self.defs)
        # We compile the assumptions and defts with the new spec so they can append any neccessary definitions. This also means that definitions and assumptions are not able to see other definitions nor assumptions
        
        console.print("[bold green]Starting Compilation...")
        
        if not self.assumptions is None:
            console.rule("[bold cyan]🏗️ Compiling Assumptions...")
            new_assumptions = [a.compile(compiled_spec) for a in self.assumptions]
            for a in new_assumptions:
                compiled_spec.assumptions.append(a)
        if not self.defs is None:
            # Precompile
            console.rule("[bold cyan]🔍 Precompiling Definitions...")
            for d in self.defs:
                d.preCompile(compiled_spec)
            # Compile
            console.rule("[bold cyan]🏗️ Compiling Definitions...")
            compiled_defs = [d.compile(compiled_spec) for d in compiled_spec.defs]
            compiled_spec.defs = []
            # Append the compiled definitions to the spec
            for d in compiled_defs:
                compiled_spec.defs.append(d)
        
        console.rule("[bold blue]🛠️ Compilation Done!")
        
        return compiled_spec

        
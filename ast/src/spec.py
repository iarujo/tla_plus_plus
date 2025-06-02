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
from src.definitions.temporal import WeakFairness

class Spec:
    
    def __init__(self, module: str, extends: List[str], constants: Constants, assumptions: Optional[List[Assume]], variables: Variables, defs: List[Definition]):
        self.module = module # The name of the module
        self.extends = extends # The modules this module extends
        self.constants = constants # The constants of the module
        self.assumptions = assumptions # The assumptions of the module
        self.variables = variables # The variables of the module
        self.defs = defs # The definitions of the module
        self.pending_updates = [] # The pending updates of the module for compilaation
    
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
        """
        Returns the Init definition for the module.
        """
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
    
    def get_node_count(self):
        """
        Returns the number of nodes in the module. We don't count all nodes, but rather only the ones which may vary in amount (i.e. the variables and the definitions)
        """
        count = 0
        # Count the number of nodes in the assumptions
        if self.assumptions is not None:
            for a in self.assumptions:
                count += a.get_node_count()
        # Count the number of variables
        if self.variables is not None:
            count += self.variables.get_node_count()
        # Count the number of nodes in the definitions
        if self.defs is not None:
            for d in self.defs:
                count += d.get_node_count()
        return count
                
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
                
                
    def precompilation_split_next_fairness(self, traces: List[List[str]]):
        """
        Splits the Next definition into two definitions: Next_Fair and Next_Unfair. This is done to enforce the right properties when compile Byzantine Comparisons.
        """
        
        def process_trace(trace: List[str]):
            """
            Splits a trace into two traces: one for the fair transitions and one for the unfair transitions.
            """
            original_def = None
            fair_def = None
            unfair_def = None          
            
            # See if the definition at the head of the trace has been split yet
            for d in self.defs:
                if d.get_name() == trace[-1]:
                    original_def = d
                if d.get_name() == f"{trace[-1]}_Fair":
                    fair_def = d
                if d.get_name() == f"{trace[-1]}_Unfair":
                    unfair_def = d
                    
            needs_splitting = original_def and not unfair_def
            if not needs_splitting:
                return
            
            print("Splitting definition", trace[-1])
            
            # Find the index of the original definition
            index = next((i for i, d in enumerate(self.defs) if d.get_name() == trace[-1]), None)
            if index is None:
                raise ValueError(f"Definition {trace[-1]} not found in self.defs")
            
            # Remove original and create new definitions
            del self.defs[index]
            # self.defs = [x for x in self.defs if x.get_name() != trace[-1]]
            fair_def = original_def.with_set_name(trace[-1] + "_Fair")
            unfair_def = original_def.with_set_name(trace[-1] + "_Unfair")
                
            # If we're dealing with Next, add another definition for the conjunction of the fair and unfair versions
            if trace[-1] == "Next":
                next_def = Definition(
                    "Next",
                    Disjunction([
                        Alias(f"{trace[-1]}_Fair", None), 
                        Alias(f"{trace[-1]}_Unfair", None)
                    ])
                )                    
                self.defs.insert(index, next_def)
                    
            # Insert the definitions into the functions
            self.defs.insert(index, unfair_def)
            self.defs.insert(index, fair_def)
        
            # If this definition calls yet another definition, make sure each of the fair/unfair functions call the right definition, then recurse
            if len(trace) > 1:
                self._process_nested_definitions(trace, fair_def, unfair_def)
                process_trace(trace[:-1])
            
            else:
                self._finalize_fairness_updates(fair_def)
                        
        
        for trace in traces:
            process_trace(trace)
            
    def _process_nested_definitions(self, trace, fair_def, unfair_def):
        """Handles nested definition updates and fairness properties."""
        print("Recursing into definition", trace[-2])
        fair_def.changeAliasTo(trace[-2], f'{trace[-2]}_Fair')
        unfair_def.changeAliasTo(trace[-2], f'{trace[-2]}_Unfair')
                
        # In the special case where the definition contains a Weak Fairness Property, we need to update it to use only the fair version of the called function
        # This will only work when the definition is a conjunction, and the Weak Fairness Property is in the top level of this conjunction:
        if(isinstance(unfair_def.value, Conjunction)):
            print("Updating Weak Fairness Properties in Unfair definition")
            for l in unfair_def.value.getLiteralsUnsafe():
                if isinstance(l, WeakFairness) and isinstance(l.action, Alias) and l.action.name == f'{trace[-2]}_Unfair':
                    print(f'Removing Weak Fairness Property {l} from Unfair definition')
                    unfair_def.value.remove_literal(l)
        else:
            print("Unfair definition is not a conjunction, cannot update Weak Fairness Properties. The resulting spec may contain false Weak Fairness Properties")
                
        self.update(fair_def)
        self.update(unfair_def)
        
    def _finalize_fairness_updates(self, fair_def):
        """Final updates to spec after fairness splitting."""
        print(f"Finalizing updates for {fair_def.get_name()}")
        
        # Have a regular comparison in the fair trace, and a byzantine one in the unfair trace
        updated_fair = fair_def.byzComparisonToNormal(self)
        self.update(updated_fair)
        
        # Finally, check if there's any Weak Fairness Properties for Next in the spec, and add them if they aren't present
        for spec_def in (d for d in self.defs if d.get_name() == "Spec"):
            if not isinstance(spec_def.value, Conjunction):
                raise ValueError("Spec definition must be a conjunction")
            
            # Update Weak Fairness properties
            wf_next = [c for c in spec_def.value.literals
                       if isinstance(c, WeakFairness)
                       and isinstance(c.action, Alias) 
                       and c.action.name == "Next"
            ]
            
            if len(wf_next) > 1:
                raise Exception(f"More than one Weak Fairness Property for Next in the spec, cannot continue with compilation")
            
            if wf_next:
                spec_def.value.remove_literal(wf_next[0])
                self.update(spec_def)
                        
            
            # WF for Next not yet defined, add it
            if not any([isinstance(c, WeakFairness) and isinstance(c.action, Alias) and c.action.name == "Next_Fair" for c in spec_def.value.getLiterals()]):
                spec_def.value.add_literal(
                    WeakFairness(Alias("Next_Fair", None), self.variables.get_variables())
                )
                self.update(spec_def)
                 
    def compile(self):
        """
        Compiles this spec into a valid TLA+ specification.
        """     
        console = Console()
        console.rule("[bold blue]🛠️ Compiler Initialized")
        
        compiled_spec = Spec(
            module = self.module, 
            extends=self.extends, 
            constants=self.constants, 
            assumptions= None if self.assumptions is None else [], 
            variables=self.variables, 
            defs = None if self.defs is None else self.defs
        )
        
        # We compile the assumptions and defts with the new spec so they can append any neccessary definitions. This also means that definitions and assumptions are not able to see other definitions nor assumptions
        console.print("[bold green]Starting Compilation...")

        # Compile assumptions
        if not self.assumptions is None:
            console.rule("[bold cyan]🏗️ Compiling Assumptions...")
            new_assumptions = [
                a.compile(compiled_spec) 
                for a in self.assumptions
            ]
            compiled_spec.assumptions.extend(new_assumptions)
            
        # Compile definitions
        if not self.defs is None:
            console.rule("[bold cyan]🔍 Precompiling Definitions...")
            for d in self.defs:
                d.preCompile(compiled_spec)
            
            console.rule("[bold cyan]🏗️ Compiling Definitions...")
            compiled_spec.defs = [
                d.compile(compiled_spec) 
                for d in compiled_spec.defs
            ]
        
        console.rule("[bold blue]🛠️ Compilation Done!")
        return compiled_spec


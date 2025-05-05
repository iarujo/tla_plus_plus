from rich.console import Console
from rich.text import Text
from typing import List
from src.spec import Spec
from src.definitions.definition import Definition
from src.definitions.clause.clause import Clause, Conjunction, Implication
from src.definitions.predicates.predicates import TRUE, FALSE,  Predicate, ArithmeticComparison, ExistentialQuantifier, In, Not
from src.definitions.terms.terms import Term, Scalar, Alias, Constant, Variable, Scalar, Constant, Alias, Variable, Function, Choose, BinaryArithmeticOp, Range
from src.definitions.terms.finiteSet import Cardinality, Set
from src.tla_plusplus.tla_plusplus_term import TLAPlusPlusTerm

class Havoc(TLAPlusPlusTerm):
    """ Sets the variables to an arbitrary value from their given sets as stated in TypeOK. """
    
    def __init__(self, vars: List[Variable], sets: List[Term], spec: Spec):
        super().__init__()
        
        # Error handling
        if len(vars) != len(sets):
            raise ValueError("The number of variables and sets must be equal.")
        if len(vars) == 0 or len(sets) == 0:
            raise ValueError("The number of variables and sets must be greater than 0.")
        if not all(isinstance(v, Variable) for v in vars):
            raise TypeError("All variables must be of type Variable.")
        if not all(isinstance(s, Term) for s in sets):
            raise TypeError("All sets must be of type Term.")
        
        self.vars = vars
        
        # Get TypeOK definitions from spec
        sets = []
        for v in self.vars:
            s = spec.get_typeok_of(v)
            if s is None:
                raise ValueError("You can only havoc variables that are defined in the spec and that have a TypeOK entry of the form VARIABLE \\in SET")
            sets.append(s)
        
        self.sets = sets
    
    def __repr__(self):
        return f"HAVOC {", ".join([repr(v) for v in self.vars])}"
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        pass
    
    def compile(self, spec: Spec):
        
        console = Console()
        console.print("[yellow]Compiling for Havoc...")
        
        def small_havoc(var: Variable, set: Term):
            """ Helper function to compile a single havoc statement. """
            return In(Alias(f"{repr(var)}'", None), set.compile(spec))
        
        # If there's only one variable, we can use the small havoc statement
        if len(self.vars) == 1:
            return small_havoc(self.vars[0], self.sets[0])
        
        # Otherwise, pack the havoc statements into a conjunction
        root = Conjunction([])
        for v, z in zip(self.vars, self.sets):
            root.add_literal(small_havoc(v, z))
        return root
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        for s in self.sets:
            s.changeAliasTo(old, new)
            
      
class Random(TLAPlusPlusTerm):
    """ Returns a random value from the set of values. """
    
    def __init__(self, set: Term):
        super().__init__()
        
        # Error handling
        if not isinstance(set, Term):
            raise TypeError("Set must be of type Term.")
        
        self.set = set
    
    def __repr__(self):
        return f"RANDOM {repr(self.set)}"
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        pass
    
    def compile(self, spec: Spec):
        console = Console()
        console.print("[yellow]Compiling for Random Term...")
        v = Alias("v", None)
        return Choose(
            var=v, 
            set=self.set.compile(spec), 
            predicate=TRUE()
        )
        
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the term to a new one.
        """
        self.set.changeAliasTo(old, new)
            
    
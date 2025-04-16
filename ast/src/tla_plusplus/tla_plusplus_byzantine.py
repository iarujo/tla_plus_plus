from typing import Union
from src.spec import Spec
from src.definitions.predicates.predicates import ArithmeticComparison, ExistentialQuantifier
from src.definitions.terms.terms import Term, Scalar, Alias, Constant, Variable, Scalar, Alias, Constant, Variable, Function, Choose, BinaryArithmeticOp, Range

NumericTerm = Union[Scalar, Alias, Constant, Variable, Function, Choose, BinaryArithmeticOp]

class ByzantineTerm(Term):
    """
    Abstract class for all terms of our extension to TLA+ that deal with simulating byzantine behaviour.
    """
    
    def __init__(self):
        super().__init__()
        
    def compile(self, spec):
        """
        Transforms the term into a valid TLA+ term.
        """
        raise NotImplementedError("This method should be implemented in subclasses.")
        
class ByzantineComparison(ByzantineTerm):
    """
    Compares a term (usally number of votes, or number of nodes) to a threshold value.
    
    Converts the code from this:
        CONSTANT MaxByzantineNodes
        ...
        variable comparison BYZANTINE threshold
    
    into this:
    
        CONSTANT MaxByzantineNodes
        ...
        \E x \in 0..MaxByzantineNodes: 
            variable comparison threshold - x
    """
    
    def __init__(self, variable: NumericTerm, comparison: ArithmeticComparison, threshold: NumericTerm):
        # Note: as there are no types per se in TLA+, we can use any type of term here and there are no guarantees that aplying the comparison operation will be valid
        super().__init__()
        self.variable = variable
        self.threshold = threshold
        self.comparison = comparison
        
    def __repr__(self):
        return f"{repr(self.variable)} {self.comparison.get_symbol(self.comparison)} BYZANTINE {self.threshold}"
    
    def compile(self, spec: Spec):
        self.__check_syntax(spec)
        x = Alias("x", None)
        MaxByzantineNodes = Alias("MaxByzantineNodes", None)
        return ExistentialQuantifier(
            variables=[x], 
            set=Range(0, MaxByzantineNodes), 
            predicate= self.comparison(
                self.variable,
                self.threshold - x
            )
        )
    
    def __check_syntax(self, spec: Spec):
        """
        Check the syntax of the Byzantine comparison term.
        """
        # Check if the variable is a scalar or an alias
        if not isinstance(self.variable, (Scalar, Alias, Constant, Variable, Scalar, Variable, Function, Choose, BinaryArithmeticOp)):
            raise TypeError("The variable must have a numeric value.")
        
        # Check if the threshold is a scalar or an alias
        if not isinstance(self.threshold, (Scalar, Alias, Constant, Variable, Scalar, Variable, Function, Choose, BinaryArithmeticOp)):
            raise TypeError("The threshold must have a numeric value.")
            
        # Check if the comparison is a valid arithmetic comparison
        if not issubclass(self.comparison, ArithmeticComparison):
            raise TypeError("The comparison must be an arithmetic comparison.")
        
        # Check is MaxByzantineNodes is in the spec's constants
        constants = spec.get_constants()
        ok = False
        for c in constants:
            if c.get_name() == "MaxByzantineNodes":
                ok = True
                break
        if not ok:
            raise ValueError("The constant MaxByzantineNodes must be defined in the spec.")
        
#class ByzantineLeader(ByzantineTerm):
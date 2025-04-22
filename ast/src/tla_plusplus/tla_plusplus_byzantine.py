from typing import Union
from src.spec import Spec
from src.definitions.definition import Definition
from src.definitions.clause.clause import Clause, Conjunction, Implication
from src.definitions.predicates.predicates import TRUE, FALSE,  Predicate, ArithmeticComparison, ExistentialQuantifier, In, Not
from src.definitions.terms.terms import Term, Scalar, Alias, Constant, Variable, Scalar, Constant, Alias, Variable, Function, Choose, BinaryArithmeticOp, Range
from src.definitions.terms.finiteSet import Cardinality, Set

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
        \\E x \\in 0..MaxByzantineNodes: 
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
        
class ByzantineLeader(ByzantineTerm):
    """
    Used to simulate a leader in a protocol that may or may not have byzantine behaviour.
    The leader changes on each round
    
    Converts the code from this:
    
        VARIABLES leaderIsByzantine
        ...
        
        // These definitions should be placed inside the code block where the behaviour mught differ
        // Note: Do not use conjunctions between the two keywords!
            HONEST LEADER <user-defined honest behaviour specification> // This is your regular protocol behaviour
            BYZANTINE LEADER <user-defined byzantine behaviour specification>
    
    into this:
    
        VARIABLES leaderIsByzantine

        LeaderTypeOK == leaderIsByzantine \\in {TRUE, FALSE}


        ...
        
        // These definitions should be placed inside the code block where the behaviour might differ
            /\\ leaderIsByzantine => <user-defined honest behaviour specification>
            /\\ ~leaderIsByzantine => <user-defined byzantine behaviour specification>
        
        ...

        Init == /\\ ...
                        ...
                        /\\ leaderIsByzantine\\in {TRUE, FALSE}
    """
    
    def __init__(self, hon_behaviour: Union[Predicate, Clause], byz_behaviour: Union[Predicate, Clause]):
        self.hon_behaviour = hon_behaviour
        self.byz_behaviour = byz_behaviour
        
    def __repr__(self):
        return f"HONEST LEADER {"\t".join([f'{l}\n' for l in repr(self.hon_behaviour).splitlines()])}\nBYZANTINE LEADER {"\t".join([f'{l}\n' for l in repr(self.byz_behaviour).splitlines()])}" # {"\\t".join([f'{l}\\n' for l in repr(self.hon_behaviour).splitlines()])}
    
    def compile(self, spec: Spec):
        self.__check_syntax(spec)
        
        leaderIsByzantine = Variable("leaderIsByzantine")
        
        # LeaderTypeOK == leaderIsByzantine \\in {TRUE, FALSE}
        LeaderTypeOK = Definition(
            name="LeaderTypeOK",
            value= In(
                left=leaderIsByzantine,
                right=Set([TRUE, FALSE])
            )
        )
        # TODO: Can convert this into another queue message
        spec.prepend_to_defs(LeaderTypeOK)
        
        Init = spec.get_init()
        if Init is not None:
            Init = Init.compile()
            if isinstance(Init.value, Conjunction):
                Init.add_clause(leaderIsByzantine.In({TRUE, FALSE}))
            else:
                Init.set_value(
                    Conjunction([
                        Init.value,
                        leaderIsByzantine.In({TRUE, FALSE})
                    ])
                )
            # Add the new Init to the spec
            spec.update_later(Init)
        
        return Conjunction([
            Implication(
                p=leaderIsByzantine,
                q=self.hon_behaviour.compile(spec)
            ),
            Implication(
                p=Not(leaderIsByzantine),
                q=self.byz_behaviour.compile(spec)
            )
        ])
        
    def __check_syntax(self, spec: Spec):
        """
        Check the syntax of the Byzantine leader term.
        """
        # Check if the variable is a scalar or an alias
        if not isinstance(self.hon_behaviour, (Predicate, Clause)):
            raise TypeError("The honest behaviour description must have a boolean value.")
        
        # Check if the threshold is a scalar or an alias
        if not isinstance(self.byz_behaviour, (Scalar, Alias, Constant, Variable, Scalar, Variable, Function, Choose, BinaryArithmeticOp)):
            raise TypeError("The byzantine behaviour description must have a boolean value.")
        
        variables = spec.get_variables()
        ok_leader = False
        if variables is None:
            raise ValueError("The variable leaderIsByzantine must be defined in the spec.")
        for v in variables:
            if v.get_name() == "leaderIsByzantine":
                ok_leader = True
                break
        if not ok_leader:
            raise ValueError("The variable leaderIsByzantine must be defined in the spec.")
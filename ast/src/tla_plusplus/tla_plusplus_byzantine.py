from typing import Union
from src.spec import Spec
from src.definitions.definition import Definition
from src.definitions.clause.clause import Clause, Conjunction, Implication
from src.definitions.predicates.predicates import Predicate, ArithmeticComparison, ExistentialQuantifier, In, Not
from src.definitions.terms.terms import Term, Scalar, Alias, Constant, Variable, Scalar, Constant, Alias, Variable, Function, Choose, BinaryArithmeticOp, Range
from src.definitions.terms.finiteSet import Cardinality

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
        
class ByzantineLeader(ByzantineTerm):
    """
    Used to simulate a leader in a protocol that may or may not have byzantine behaviour.
    The leader changes on each round
    
    Converts the code from this:
    
        VARIABLES LEADER, Acceptors, MaxByzantineNodes // Use Acceptors keyword to indincate that's your set of honest acceptors, these are the participants of your protocol

        ...
        
        // These definitions should be placed inside the code block where the behaviour mught differ
        // Note: Do not use conjunctions between the two keywords!
            HONEST LEADER <user-defined honest behaviour specification> // This is your regular protocol behaviour
            BYZANTINE LEADER <user-defined byzantine behaviour specification>
    
    into this:
    
        VARIABLES LEADER, Acceptors, MaxByzantineNodes

        LEADER \in {0..(Cardinality(Acceptors) + MaxByzantineNodes)}

        leaderIsByzantine = LEADER >= Cardinality(Acceptors)

        ...

        // These definitions should be placed inside the code block where the behaviour mught differ
            /\ leaderIsByzantine => <user-defined honest behaviour specification>
            /\ ~leaderIsByzantine => <user-defined byzantine behaviour specification>
    
    """
    
    def __init__(self, hon_behaviour: Union[Predicate, Clause], byz_behaviour: Union[Predicate, Clause]):
        self.hon_behaviour = hon_behaviour
        self.byz_behaviour = byz_behaviour
        
    def __repr__(self):
        return f"HONEST LEADER {"\t".join([f'{l}\n' for l in repr(self.hon_behaviour).splitlines()])}\nBYZANTINE LEADER {"\t".join([f'{l}\n' for l in repr(self.byz_behaviour).splitlines()])}" # {"\t".join([f'{l}\n' for l in repr(self.hon_behaviour).splitlines()])}
    
    def compile(self, spec: Spec):
        self.__check_syntax(spec)
        
        LEADER = Variable("LEADER")
        Acceptors = Constant("Acceptors")
        MaxByzantineNodes = Constant("MaxByzantineNodes")
        
        # LEADER \in {0..(Cardinality(Acceptors) + MaxByzantineNodes)}
        LeaderTypeOK = Definition(
            name="LeaderTypeOK",
            value= In(
                left=LEADER,
                right=Range(Scalar(0), Cardinality(Acceptors)) + MaxByzantineNodes
            )
        )
        spec.prepend_to_defs(LeaderTypeOK)
        
        # leaderIsByzantine == LEADER >= Cardinality(Acceptors)
        leaderIsByzantine = Definition(
            name="leaderIsByzantine",
            value=LEADER >= Cardinality(Acceptors)
        )
        spec.prepend_to_defs(leaderIsByzantine)
        
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
        
        # Check is MaxByzantineNodes is in the spec's constants
        constants = spec.get_constants()
        ok_acceptor = False
        ok_maxbyznodes = False
        for c in constants:
            if c.get_name() == "Acceptors":
                ok_acceptor = True
            if c.get_name() == "MaxByzantineNodes":
                ok_maxbyznodes = True
            if ok_leader and ok_acceptor and ok_maxbyznodes:
                break
            
        # TODO: use string formats to reduce the size of this code
        if not ok_acceptor:
            if not ok_maxbyznodes:
                raise ValueError("The constants MaxByzantineNodes and Acceptor must be defined in the spec.")
            else:
                raise ValueError("The constant Acceptor must be defined in the spec.")
        if not ok_maxbyznodes:
            raise ValueError("The constant MaxByzantineNodes must be defined in the spec.")
        
        variables = spec.get_variables()
        ok_leader = False
        for v in variables:
            if v.get_name() == "LEADER":
                ok_leader = True
                break
        if not ok_leader:
            raise ValueError("The variable LEADER must be defined in the spec.")
import typing
from src.spec import Spec
from src.definitions.definition import Definition
from src.definitions.clause.clause import Clause, Conjunction, Implication
from src.definitions.predicates.predicates import TRUE, FALSE,  Predicate, ArithmeticComparison, ExistentialQuantifier, In, Not
from src.definitions.terms.terms import Term, Scalar, Alias, Constant, Variable, Scalar, Constant, Alias, Variable, Function, Choose, BinaryArithmeticOp, Range, String
from src.definitions.terms.finiteSet import Cardinality, Set, Union
from src.tla_plusplus.tla_plusplus_term import TLAPlusPlusTerm

NumericTerm = typing.Union[Scalar, Alias, Constant, Variable, Function, Choose, BinaryArithmeticOp]
        
class ByzantineComparison(TLAPlusPlusTerm):
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
        
class ByzantineLeader(TLAPlusPlusTerm):
    """
    Used to simulate a leader in a protocol that may or may not have byzantine behaviour.
    Agnostic to the number of byzantine nodes in the protocol.
    The leader changes on each round
    
    Converts the code from this:
    
        VARIABLES king // Let this be the variable used to model the leader in the original spec
        ...
        
        // These definitions should be placed inside the code block where the behaviour mught differ
        // Note: Do not use conjunctions between the two keywords!
            HONEST LEADER <user-defined honest behaviour specification> // This is your regular protocol behaviour
            BYZANTINE LEADER <user-defined byzantine behaviour specification>
    
    into this:
    
        VARIABLES king

        TypeOK == /\ ...
					...
					/\ king \in (<Original Set> \cup {"byzantine"})
					
        leaderIsByzantine == king \in {"byzantine"}

        ...
        
        // These definitions should be placed inside the code block where the behaviour might differ
            /\\ leaderIsByzantine => <user-defined honest behaviour specification>
            /\\ ~leaderIsByzantine => <user-defined byzantine behaviour specification>
        
        ...

        Init == /\\ ...
                        ...
                        /\\ king \in (<Original Set> \cup {"byzantine"})
    """
    
    def __init__(self, hon_behaviour: typing.Union[Predicate, Clause], byz_behaviour: typing.Union[Predicate, Clause]):
        self.hon_behaviour = hon_behaviour
        self.byz_behaviour = byz_behaviour
        
    def __repr__(self):
        return f"HONEST LEADER {repr(self.hon_behaviour)} /\ BYZANTINE LEADER {repr(self.byz_behaviour)}"
    
    def compile(self, spec: Spec):
        self.__check_syntax(spec)
        
        # TODO: make a different version where leaderIsByzantine doesn't exist, and we just add one more state ("byzantine") to the states from king
        king = Variable("king")
        
        # leaderIsByzantine == king \in {"byzantine"}
        leaderIsByzantine = Definition(
            name="leaderIsByzantine",
            value= In(
                left=king,
                right=Set([String("byzantine")])
            )
            
        )
        spec.update_later(leaderIsByzantine)
        
        def change_king_definition(king: Variable, definition: Definition):
            
            if definition is None:
                raise ValueError(f"The {definition.get_name()} definition must be defined in the spec.")
                
            # Compile Init
            definition = definition.compile(spec)
            if not isinstance(definition.value, Conjunction):
                raise ValueError(f"The {definition.get_name()} definition must be a conjunction.")
            
            con = definition.value
            changedKing= False
            # Find where king is defined in the Init definition
            for i, l in enumerate(con.literals):
                if isinstance(l, In) and repr(l.left) == repr(king):
                    con.literals[i] = In(
                            left=king,
                            right=Union(l.right, Set([String("byzantine")]))
                        )
                    changedKing = True
                    
            if not changedKing:
                raise ValueError(f"The {definition.get_name()} definition must contain the variable king inside a statement of the form king \\in SET.")

            definition.set_value(con)
            # Add the new Init to the spec
            spec.update_later(definition)
            
        
        # TypeOK is changed to accomodate for byzantine nodes
        change_king_definition(king, spec.get_typeok())
        
        # Init is changed to accomodate for byzantine nodes
        change_king_definition(king, spec.get_init())
        
        return Conjunction([
            Implication(
                p=Not(Alias("leaderIsByzantine", None)),
                q=self.hon_behaviour.compile(spec)
            ),
            Implication(
                p=Alias("leaderIsByzantine", None),
                q=self.byz_behaviour.compile(spec)
            )
        ])
        
    def __check_syntax(self, spec: Spec):
        """
        Check the syntax of the Byzantine leader term.
        """
        
        if not isinstance(self.hon_behaviour, (Predicate, Clause)):
            raise TypeError("The honest behaviour description must have a boolean value.")
        
        # Check if the threshold is a scalar or an alias
        if not isinstance(self.byz_behaviour, (Predicate, Clause)):
            raise TypeError("The byzantine behaviour description must have a boolean value.")
        
        variables = spec.get_variables()
        ok_leader = False
        if variables is None:
            raise ValueError("The variable king must be defined in the spec.")
        for v in variables:
            if repr(v) == "king":
                ok_leader = True
                break
        if not ok_leader:
            raise ValueError("The variable king must be defined in the spec.")
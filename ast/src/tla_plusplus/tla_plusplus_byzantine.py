import typing
from rich.console import Console
from rich.text import Text
from src.spec import Spec
from src.definitions.definition import Definition
from src.definitions.clause.clause import Clause, Conjunction, Implication
from src.definitions.predicates.predicates import TRUE, FALSE,  Predicate, ArithmeticComparison, ExistentialQuantifier, In, Not
from src.definitions.terms.terms import Term, Scalar, Alias, Constant, Variable, Scalar, Constant, Alias, Variable, Function, Choose, BinaryArithmeticOp, Range, String, Addition, Substraction, Multiplication, Division, BinaryArithmeticOp
from src.definitions.terms.finiteSet import Cardinality, Set, Union
from src.tla_plusplus.tla_plusplus_term import TLAPlusPlusTerm

NumericTerm = typing.Union[Scalar, Alias, Constant, Variable, Function, Choose, BinaryArithmeticOp]
Trace = typing.List[typing.Union[typing.List[str]]] # Trace of definitions that call each other, ending up in the expression containing the Byzantine term. List[0] is the closest function calling the Byzantine term, and the last element is the paremt of the previous functions. All traces must end in Next
        
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
    
    def __init__(self, variable: NumericTerm, comparison: ArithmeticComparison, threshold: NumericTerm, inNext: bool, trace: Trace):
        # Note: as there are no types per se in TLA+, we can use any type of term here and there are no guarantees that aplying the comparison operation will be valid
        super().__init__()
        self.variable = variable
        self.threshold = threshold
        self.comparison = comparison
        self.inNext = inNext # Wether the construct is in the Next definition or not, aka, if we need to split Next
        self.trace = trace
        
    def __repr__(self):
        return f"{repr(self.variable)} {self.comparison.get_symbol(self.comparison)} BYZANTINE {self.threshold}"
    
    def get_node_count(self):
        """
        Returns the number of nodes in the Byzantine comparison.
        """
        return self.variable.get_node_count() + self.threshold.get_node_count() + 1
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        
        console = Console()
        console.print("[yellow]Precompiling for Byzantine Comparison...")
        
        if not self.inNext or self.trace is None:
            console.print("[green]Precompiling for Byzantine Comparison Done!")
            return 
        
        spec.precompilationSplitNextFairness(self.trace)
        
        console.print("[green]Precompiling for Byzantine Comparison Done!")
    
    def compile(self, spec: Spec):
        console = Console()
        console.print("[yellow]Compiling for Byzantine Comparison...")
        self.__check_syntax(spec)
        x = Alias("x", None)
        MaxByzantineNodes = Alias("MaxByzantineNodes", None)
        return ExistentialQuantifier(
            variables=[x], 
            set=Range(Scalar(0), MaxByzantineNodes), 
            predicate= self.comparison(
                self.variable,
                self.threshold - x
            )
        )
        
    def byzComparisonToNormal(self, spec: Spec):
        print("[yellow]Converting Byzantine Comparison to normal...")
        return self.comparison(
            self.variable,
            self.threshold
        )
    
    def __check_syntax(self, spec: Spec):
        """
        Check the syntax of the Byzantine comparison term.
        """
        console = Console()
        
        # Check if the variable is a scalar or an alias
        if not isinstance(self.variable, (Cardinality, Alias)):
            raise TypeError(f'The variable {self.variable} must be either the Cardinality of the set of votes or voters or an Alias of a definition including the cardinaility of this same set.')
        
        def isLinearCombinationOfConstants(term: Term) -> bool:
            """
            Check if the term is a linear combination of constants.
            """
            if isinstance(term, (Constant, Scalar)):
                return True
            elif isinstance(term, BinaryArithmeticOp):
                return isLinearCombinationOfConstants(term.a) and isLinearCombinationOfConstants(term.b)
            elif isinstance(term, Alias):
                # In this case, only a weak check is done
                console.print("[red]Warning: The alias {term} is not guaranteed to be a linear combination of constants. This may lead to unexpected results.")
                return True
                
            return False
        
        # Check if the threshold is a scalar or an alias
        if not isLinearCombinationOfConstants(self.threshold):
            raise TypeError(f'The threshold {self.threshold} must be a Constant or a function of Constants.')
        
            
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
        
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the temporal predicate to a new one.
        """
        self.variable.changeAliasTo(old, new)
        self.threshold.changeAliasTo(old, new)
        
        
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
            MODE 1 <user-defined mode 1 behaviour specification> // This is your regular protocol behaviour
            MODE 2 <user-defined mode 2 behaviour specification>
    
    into this:
    
        VARIABLES king

        TypeOK == /\\ ...
					...
					/\\ king \\in (<Original Set> \\cup {"mode 2"})
					
        pickModeTwo == king \\in {"mode 2"}

        ...
        
        // These definitions should be placed inside the code block where the behaviour might differ
            /\\ pickModeTwo => <user-defined honest behaviour specification>
            /\\ ~pickModeTwo => <user-defined byzantine behaviour specification>
        
        ...

        Init == /\\ ...
                        ...
                        /\\ king \\in (<Original Set> \\cup {"mode 2"})
    """
    
    def __init__(self, hon_behaviour: typing.Union[Predicate, Clause], byz_behaviour: typing.Union[Predicate, Clause]):
        self.hon_behaviour = hon_behaviour
        self.byz_behaviour = byz_behaviour
        
    def __repr__(self):
        return f"MODE 1 {repr(self.hon_behaviour)} /\\ MODE 2 {repr(self.byz_behaviour)}"
    
    def get_node_count(self):
        """
        Returns the number of nodes in the Byzantine leader.
        """
        return self.hon_behaviour.get_node_count() + self.byz_behaviour.get_node_count() + 1
    
    def preCompile(self, spec: Spec):
        """
        Make changes to the original Spec before compiling it. This method helps minimize recursive calls.
        """
    
        console = Console()
        console.print("[yellow]Precompiling for Byzantine Leader...")
                
        self.__check_syntax(spec)
        
        king = Variable("king")
        
        def change_king_definition(king: Variable, definition: Definition):
            
            if definition is None:
                raise ValueError(f"The {definition.get_name()} definition must be defined in the spec.")
                
            # Compile
            # definition = definition.compile(spec)
            # Case where king is the only variable
            if isinstance(definition.value, In):
                definition.value = Conjunction([definition.value])
            # Make sure the definition is a conjunction, otherwise, the king's state space won't be updated
            if not isinstance(definition.value, Conjunction):
                console.print(f"[red]⚠️ The [bold]{definition.get_name()}[/bold] definition is not a conjunction nor an \\in statement. No updates will be made to the king's state space.")
                return
            
            con = definition.value
            changedKing= False
                
            for i, l in enumerate(con.literals):
                if isinstance(l, In) and repr(l.left) == repr(king):
                    con.literals[i] = In(
                            left=king,
                            right=Union(l.right, Set([String("mode 2")]))
                        )
                    changedKing = True
                    
            if changedKing:
                console.print(f"[green]✅ Updated the king's state space in the definition [bold]{definition.get_name()}[/bold].")
            else: 
                console.print(f"[red]⚠️ The [bold]{definition.get_name()}[/bold] definition didn't contain the variable [bold]king[/bold] inside a statement like [italic]king ∈ SET[/italic]. No changes made.")


            definition.set_value(con)
            # Add the new Init to the spec
            spec.update(definition)
            
        # Get all defs from the spec
        defs = spec.get_definitions()
        
        for d in defs:
            change_king_definition(king, d)
            
        # pickModeTwo == king \in {"mode 2"}
        pickModeTwo = Definition(
            name="pickModeTwo",
            value= In(
                left=king,
                right=Set([String("mode 2")])
            )
            
        )
        spec.update(pickModeTwo)
            
        console.print("[green]Precompiling for Byzantine Leader Done!")
    
    def compile(self, spec: Spec):
        
        console = Console()
        console.print("[yellow]Compiling for Byzantine Leader...")
        
        def change_king_definition(king: Variable, expr: Definition):
            if isinstance(expr, In):
                    expr= Conjunction([expr])
            # Make sure the definition is a conjunction, otherwise, the king's state space won't be updated
            if not isinstance(expr, Conjunction):
                return
                
            con = expr
            changedKing= False
                    
            for i, l in enumerate(con.literals):
                if isinstance(l, In) and repr(l.left) == repr(king):
                    con.literals[i] = In(
                            left=king,
                            right=Union(l.right, Set([String("mode 2")]))
                        )
                    changedKing = True
            if changedKing:
                console.print(f"[green]✅ Updated the king's state space in the definition [bold]{expr}[/bold].")
                
        change_king_definition(Alias("king'", None), self.hon_behaviour)
        change_king_definition(Alias("king'", None), self.byz_behaviour)
        
        return Conjunction([
            Implication(
                p=Not(Alias("pickModeTwo", None)),
                q=self.hon_behaviour.compile(spec)
            ),
            Implication(
                p=Alias("pickModeTwo", None),
                q=self.byz_behaviour.compile(spec)
            )
        ])
        
    def byzComparisonToNormal(self, spec: Spec):
        
        return ByzantineLeader(
            hon_behaviour=self.hon_behaviour.byzComparisonToNormal(spec),
            byz_behaviour=self.byz_behaviour.byzComparisonToNormal(spec)
        )
        
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
        
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the temporal predicate to a new one.
        """
        self.hon_behaviour.changeAliasTo(old, new)
        self.byz_behaviour.changeAliasTo(old, new)

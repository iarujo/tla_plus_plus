from src.spec import Spec
from src.variables.variables import Variables
from src.constants.constants import Constants
from src.assume.assume import Assume
from src.definitions.definition import Definition
from src.definitions.clause.clause import Conjunction, Disjunction, Implication
from src.definitions.predicates.predicates import TRUE, FALSE, UniversalQuantifier, ExistentialQuantifier, Not, In, SubsetEquals, Equals, NotEquals, LessThan, LessThanEquals, GreaterThan, GreaterThanEquals
from src.definitions.terms.terms import Constant, Variable, Scalar, String, Alias, Unchanged, Enabled, Choose, Range, Addition, Substraction, Multiplication, Division
from src.definitions.terms.records import Record, RecordInstance, Mapping
from src.definitions.terms.finiteSet import Subset, Set, SetOf, SetFrom, SetExcept, IndexSet, Cardinality, Union, Intersection
from src.definitions.temporal import Box, Diamond, FrameCondition, WeakFairness
from src.tla_plusplus.tla_plusplus_byzantine import ByzantineComparison

def bv_ast():
    
    name="BVBroadcastByzantine"
    extends=["Integers", "FiniteSets"]  #TODO: Create a constant for Integers and FiniteSets (E.G Module Names or smth)
    
    # Define constants
    Acceptors = Constant("Acceptors")
    T = Constant("T")
    MaxByzantineNodes = Constant("MaxByzantineNodes")
    
    constants=Constants([Acceptors, T, MaxByzantineNodes])
    
    # Define variables
    network = Variable("network")
    binValues = Variable("binValues")
    
    vars = Variables([network, binValues])
    
    # Aliases
    a = Alias("a", None)
    v = Alias("v", None)
    m = Alias("m", None)
    
    # Definitions
    
    Values = Definition(
        name="Values", 
        value=Set([Scalar(0), Scalar(1)])
    )
        
    Message = Definition(
        name="Message", 
        value=Record(
            ["acc", "val"], 
            [Union(Acceptors, Set([String("init")])), Alias("Values", None)]
        )
    )

    TypeOK = Definition(
        name="TypeOK", 
        value=Conjunction([
            SubsetEquals(network, Alias("Message", None)),
            In(binValues, Mapping([Acceptors], [Union(Alias("Nat", None), Set([Scalar(-1)]))]))
        ])
    )
    
    Count = Definition(
        name="Count", 
        arguments=[v],
        value=Cardinality(
            SetOf(
                var=m,
                set=network,
                predicate=Equals(Alias("m.val", None), v)
            )
        )
    )
    
    HasSent = Definition(
        name="HasSent", 
        arguments=[a, v],
        value=ExistentialQuantifier(
            variables=[m],
            set=network,
            predicate=Conjunction([
                Equals(Alias("m.acc", None), a),
                Equals(Alias("m.val", None), v)
            ])
        )
    )
    
    Send = Definition(
        name="Send", 
        arguments=[m],
        value=Equals(
            Alias("network'", None),
            Union(
                Alias("network", None),
                Set([m])
            )
        )
    )
    
    Init = Definition(
        name="Init", 
        value=Conjunction([
            Equals(network, Set([RecordInstance(["acc", "val"], [String("init"), Scalar(0)]), RecordInstance(["acc", "val"], [String("init"), Scalar(1)])])),
            Equals(binValues, RecordInstance([In(a, Acceptors)], [Scalar(-1)])),
        ])
    )
    
    Next = Definition(
        name="Next", 
        value=Disjunction([
            ExistentialQuantifier(
                variables=[a],
                set=Acceptors,
                predicate=ExistentialQuantifier(
                    variables=[v],
                    set=Alias("Values", None),
                    predicate=Conjunction([
                        Not(Alias("HasSent", [a, v])),
                        ByzantineComparison(Alias("Count", [v]), GreaterThan, T),
                        Alias("Send", [RecordInstance(["acc", "val"], [a, v])]),
                        Unchanged(binValues)
                    ])
                )
            ),
            ExistentialQuantifier(
                variables=[a],
                set=Acceptors,
                predicate=ExistentialQuantifier(
                    variables=[v],
                    set=Alias("Values", None),
                    predicate=Conjunction([
                        ByzantineComparison(Alias("Count", [v]), GreaterThan, (Scalar(2)*T)+Scalar(1)),
                        Equals(Alias("binValues'", None), SetExcept(
                            set=binValues,
                            index=a,
                            value=v
                        )),
                        Unchanged(network)
                    ])
                )
            ),
        ])
    )
    
    _Spec = Definition(
        name="Spec", 
        value=Conjunction([
            Alias("Init", None),
            Box(
                    FrameCondition(
                        Alias("Next", None),
                        [network, binValues],
                    )
                ),
        ])
    )
    
    defs = [
       Values, Message, TypeOK, Count, HasSent, Send, Init, Next, _Spec
    ]
    spec = Spec(module=name, extends=extends, constants=constants, assumptions=[], variables=vars, defs=defs)
    
    return spec
    
print(bv_ast().compile())
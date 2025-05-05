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
from src.tla_plusplus.tla_plusplus_byzantine import ByzantineComparison, ByzantineLeader
from src.tla_plusplus.tla_plusplus_syntactic_sugar import Random
from comparison_metrics import compare_asts

def king_ast():    
    # AST of the original spec
    
    extends = ["Integers", "FiniteSets"]
    
    # Constants
    Acceptors = Constant("Acceptors")
    Values = Constant("Values")
    F = Constant("F")
    consts = Constants([Acceptors, Values, F])
    
    # Variables
    network = Variable("network")
    value = Variable("value")
    king = Variable("king")
    leaderIsByzantine = Variable("leaderIsByzantine")
    vars = Variables([network, value, king, leaderIsByzantine])
    
    # Assumptions
    assum = Assume(
        name="FAssumption",
        expr= F <= (Cardinality(Acceptors) / Scalar(3)),
    )
    
    # Aliases
    a = Alias("a", None)
    b = Alias("b", None)
    c = Alias("c", None)
    v = Alias("v", None)
    m = Alias("m", None)
    e = Alias("e", None)
    p = Alias("p", None)
    x = Alias("x", None)
    a1 = Alias("a1", None)
    a2 = Alias("a2", None)
    c1 = Alias("c1", None)
    c2 = Alias("c2", None)
    v1 = Alias("v1", None)
    v2 = Alias("v2", None)
    va = Alias("va", None)
    vb = Alias("vb", None)
    ve = Alias("ve", None)
    m1 = Alias("m1", None)
    m2 = Alias("m2", None)
    vals = Alias("vals", None)
    threshold = Alias("threshold", None)
    typ = Alias("typ", None)
    Q = Alias("Q", None)
    
    # Definitions
        
    Message = Definition(
        name="Message", 
        value=Record(
            ["type", "acc", "val"], 
            [Set([String("broadcast"), String("propose")]), Acceptors, Values])
    )
    

    TypeOK = Definition(
        name="TypeOK",
        value=Conjunction([
            SubsetEquals(network, Alias("Message", None)),
            In(value, Mapping([Acceptors], [Values])),
            In(king, Acceptors),
        ])
    )
    
    Broadcast = Definition(
        name="Broadcast",
        value=Union(
            a=network,
            b=Set([RecordInstance(
                ["type", "acc", "val"], 
                [String("broadcast"), a, v],
            )])
        ),
        arguments=(a, v),
    )
    
    Propose = Definition(
        name="Propose",
        value=Union(
            a=network,
            b=Set([RecordInstance(
                ["type", "acc", "val"], 
                [String("propose"), a, v],
            )])
            ),
        arguments=(a, v)
    )
    
    AgreedValues = Definition(
        name="AgreedValues",
            value=SetOf(
                var=v,
                set=Values,
                predicate=ExistentialQuantifier(
                variables=[Q],
                set=Subset(Acceptors),
                predicate=Conjunction([
                    Cardinality(Q) >= threshold, # Add byzantine comparison here
                    UniversalQuantifier(
                        variables=[a1],
                        set=Q,
                        predicate=In(RecordInstance(
                                        ["type", "acc", "val"], 
                                        [typ, a1, v],
                                    ),
                                    network
                                )
                    )
                ])
                )  
            ),
        arguments=[typ, threshold],
        
    )
    
    BroadcastAgreedValues = Definition(
        name="BroadcastAgreedValues",
        value=Alias(
            name="AgreedValues", 
            arguments=[
                String("broadcast"),
                Cardinality(Acceptors) - F
            ]
        ),
    )
    
    ProposeAgreedValues = Definition(
        name="ProposeAgreedValues",
        value=Alias(
            name="AgreedValues", 
            arguments=[
                String("propose"),
                F + 1
            ]
        ),
    )
    
    RoundOne = Definition(
        name="RoundOne",
        value=Conjunction([
            Equals(Alias("network'", None), Alias("Broadcast", [a, IndexSet(value, a)])),
            Unchanged(value),
            Unchanged(king),
        ]),
        arguments=[a]
    )
    
    RoundTwo = Definition(
        name="RoundTwo",
        value=Disjunction([
            Conjunction([
                Cardinality(Alias("BroadcastAgreedValues", None)) > Scalar(0),
                Equals(Alias("network'", None), Alias("Propose", [a, Choose(v, Alias("BroadcastAgreedValues", None), TRUE())])),
                Unchanged(value),
                Unchanged(king),
                Unchanged(leaderIsByzantine),
                ]),
            Conjunction([
                Cardinality(Alias("ProposeAgreedValues", None)) > Scalar(0),
                Equals(Alias("value'", None), SetExcept(value, a, Choose(v, Alias("ProposeAgreedValues", None), TRUE()))),
                Unchanged(network),
                Unchanged(king),
                ]),
        ]),
        arguments=[a]
    )
        
    RoundThree = Definition(
        name="RoundThree",
        value=Conjunction([
            Cardinality(Alias("AgreedValues", [String("propose"), Cardinality(Acceptors) - F])) == Scalar(0),
            Equals(Alias("value'", None), SetExcept(value, a, IndexSet(value, king))),
            Unchanged(network),
            Unchanged(king),
        ]),
        arguments=[a]
    )
    
    Init = Definition(
        name="Init",
        value=Conjunction(
            [
                Equals(network, Set([])),
                In(
                    value,
                    Mapping(
                        [Acceptors],
                        [Values],
                    ),
                ),
                In(
                    king,
                    Acceptors,
                ),
            ],
        ),
    )
    
    Next = Definition(
        name="Next",
        value=Disjunction(
            [
                ExistentialQuantifier(
                    [a],
                    Acceptors,
                    Alias("RoundOne", [a])),
                ExistentialQuantifier(
                    [a],
                    Acceptors,
                    Alias("RoundTwo", [a])),
                ExistentialQuantifier(
                    [a],
                    Acceptors,
                    Alias("RoundThree", [a])),
            ],
        ),
    )
    
    _Spec = Definition(
        name="Spec",
        value=Conjunction(
            [
                Alias("Init", None),
                Box(
                    FrameCondition(
                        Alias("Next", None),
                        [network, value, king],
                    )
                ),
                WeakFairness(
                    Alias("Next", None),
                    [network, value, king],
                ),
            ],
        ),
    )
    
    definitions = [Message, TypeOK, Broadcast, Propose, AgreedValues, BroadcastAgreedValues, ProposeAgreedValues, RoundOne, RoundTwo, RoundThree, Init, Next, _Spec]
    
    spec = Spec(module="KingAlgorithm", extends=extends, constants=consts, assumptions=[assum], variables=vars, defs=definitions)
    
    return spec 

def king_ast_byzantine():    
    # AST of the original spec
    
    extends = ["Integers", "FiniteSets"]
    
    # Constants
    Acceptors = Constant("Acceptors")
    Values = Constant("Values")
    F = Constant("F")
    MaxByzantineNodes = Constant("MaxByzantineNodes")
    consts = Constants([Acceptors, Values, F, MaxByzantineNodes])
    
    # Variables
    network = Variable("network")
    value = Variable("value")
    king = Variable("king")
    vars = Variables([network, value, king])
    
    # Assumptions
    assum = Assume(
        name="FAssumption",
        expr= F <= ((Cardinality(Acceptors) + MaxByzantineNodes) / Scalar(3)),
    )
    
    # Aliases
    a = Alias("a", None)
    b = Alias("b", None)
    c = Alias("c", None)
    v = Alias("v", None)
    m = Alias("m", None)
    e = Alias("e", None)
    p = Alias("p", None)
    x = Alias("x", None)
    a1 = Alias("a1", None)
    a2 = Alias("a2", None)
    c1 = Alias("c1", None)
    c2 = Alias("c2", None)
    v1 = Alias("v1", None)
    v2 = Alias("v2", None)
    va = Alias("va", None)
    vb = Alias("vb", None)
    ve = Alias("ve", None)
    m1 = Alias("m1", None)
    m2 = Alias("m2", None)
    vals = Alias("vals", None)
    threshold = Alias("threshold", None)
    typ = Alias("typ", None)
    Q = Alias("Q", None)
    
    # Definitions
    
    Participants = Definition(
        name="Participants",
        value=Cardinality(Acceptors) + MaxByzantineNodes,
    )
        
    Message = Definition(
        name="Message", 
        value=Record(
            ["type", "acc", "val"], 
            [Set([String("broadcast"), String("propose")]), Acceptors, Values])
    )
    

    TypeOK = Definition(
        name="TypeOK",
        value=Conjunction([
            SubsetEquals(network, Alias("Message", None)),
            In(value, Mapping([Acceptors], [Values])),
            In(king, Acceptors),
        ])
    )
    
    Broadcast = Definition(
        name="Broadcast",
        value=Union(
            a=network,
            b=Set([RecordInstance(
                ["type", "acc", "val"], 
                [String("broadcast"), a, v],
            )])
        ),
        arguments=(a, v),
    )
    
    Propose = Definition(
        name="Propose",
        value=Union(
            a=network,
            b=Set([RecordInstance(
                ["type", "acc", "val"], 
                [String("propose"), a, v],
            )])
            ),
        arguments=(a, v)
    )
    
    AgreedValues = Definition(
        name="AgreedValues",
            value=SetOf(
                var=v,
                set=Values,
                predicate=ExistentialQuantifier(
                variables=[Q],
                set=Subset(Acceptors),
                predicate=Conjunction([
                    ByzantineComparison(Cardinality(Q), GreaterThanEquals ,threshold, True, [["AgreedValues", "BroadcastAgreedValues", "RoundTwo", "Next"], ["AgreedValues", "ProposeAgreedValues", "RoundTwo", "Next"]]), # Add byzantine comparison here
                    UniversalQuantifier(
                        variables=[a1],
                        set=Q,
                        predicate=In(RecordInstance(
                                        ["type", "acc", "val"], 
                                        [typ, a1, v],
                                    ),
                                    network
                                )
                    )
                ])
                )  
            ),
        arguments=[typ, threshold],
        
    )
    
    BroadcastAgreedValues = Definition(
        name="BroadcastAgreedValues",
        value=Alias(
            name="AgreedValues", 
            arguments=[
                String("broadcast"),
                Alias("Participants", None) - F
            ]
        ),
    )
    
    ProposeAgreedValues = Definition(
        name="ProposeAgreedValues",
        value=Alias(
            name="AgreedValues", 
            arguments=[
                String("propose"),
                F + 1
            ]
        ),
    )
    
    RoundOne = Definition(
        name="RoundOne",
        value=Conjunction([
            Equals(Alias("network'", None), Alias("Broadcast", [a, IndexSet(value, a)])),
            Unchanged(value),
            Unchanged(king),
        ]),
        arguments=[a]
    )
    
    RoundTwo = Definition(
        name="RoundTwo",
        value=Disjunction([
            Conjunction([
                Cardinality(Alias("BroadcastAgreedValues", None)) > Scalar(0),
                Equals(Alias("network'", None), Alias("Propose", [a, Choose(v, Alias("BroadcastAgreedValues", None), TRUE())])),
                Unchanged(value),
                Unchanged(king),
                ]),
            Conjunction([
                Cardinality(Alias("ProposeAgreedValues", None)) > Scalar(0),
                Equals(Alias("value'", None), SetExcept(value, a, Choose(v, Alias("ProposeAgreedValues", None), TRUE()))),
                Unchanged(network),
                Unchanged(king),
                ]),
        ]),
        arguments=[a]
    )
        
    RoundThree = Definition(
        name="RoundThree",
        value=Conjunction([
            Cardinality(Alias("AgreedValues", [String("propose"), Alias("Participants", None) - F])) == Scalar(0),
            ByzantineLeader(
                hon_behaviour=Alias("value'", None) == SetExcept(value, a, IndexSet(value, king)), 
                byz_behaviour=Alias("value'", None) == SetExcept(value, a, Random(Values)),
            ),
            Unchanged(network),
            Unchanged(king),
        ]),
        arguments=[a]
    )
    
    Init = Definition(
        name="Init",
        value=Conjunction(
            [
                Equals(network, Set([])),
                In(
                    value,
                    Mapping(
                        [Acceptors],
                        [Values],
                    ),
                ),
                In(
                    king,
                    Acceptors,
                ),
            ],
        ),
    )
    
    Next = Definition(
        name="Next",
        value=Disjunction(
            [
                ExistentialQuantifier(
                    [a],
                    Acceptors,
                    Alias("RoundOne", [a])),
                ExistentialQuantifier(
                    [a],
                    Acceptors,
                    Alias("RoundTwo", [a])),
                ExistentialQuantifier(
                    [a],
                    Acceptors,
                    Alias("RoundThree", [a])),
            ],
        ),
    )
    
    _Spec = Definition(
        name="Spec",
        value=Conjunction(
            [
                Alias("Init", None),
                Box(
                    FrameCondition(
                        Alias("Next", None),
                        [network, value, king],
                    )
                ),
                WeakFairness(
                    Alias("Next", None),
                    [network, value, king],
                ),
            ],
        ),
    )
    
    definitions = [Participants, Message, TypeOK, Broadcast, Propose, AgreedValues, BroadcastAgreedValues, ProposeAgreedValues, RoundOne, RoundTwo, RoundThree, Init, Next, _Spec]
    
    spec = Spec(module="KingAlgorithm", extends=extends, constants=consts, assumptions=[assum], variables=vars, defs=definitions)
    
    return spec

if __name__ == "__main__":
    compare_asts(king_ast_byzantine(), king_ast_byzantine().compile())
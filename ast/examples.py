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

def test_header():
    """ Ensure a simple spec witha  header is created correctly """
    
    extends = ["Integers", "FiniteSets"]
    consts = Constants([Constant("Values"), Constant("Acceptor"), Constant("Quorum")])
    vars = Variables([Variable("network"), Variable("decided")])
    
    spec = Spec(module="MySpec", extends=extends, constants=consts, assumptions=None, variables=vars, defs=[])
    
    print(repr(spec))
    
def test_one_round_honest_quorum():
    """ Replicate the OneRoundHonestQuorum specification from the repo """
    
    Values = Constant("Values")
    Acceptor = Constant("Acceptor")
    Quorum = Constant("Quorum")
    
    network = Variable("network")
    decided = Variable("decided")
    
    extends = ["Integers", "FiniteSets"]
    consts = Constants([Values, Acceptor, Quorum])
    assumption = Assume("QuorumAssumption", Conjunction([Quorum <= Scalar(3), Quorum > (Scalar(3) / Scalar(2))])) # TODO: Add Cardinality Function
    vars = Variables([network, decided])
    
    # Definitions
    
    Q = Alias("Q", None)
    a1 = Alias("a1", None)
    v = Alias("v", None)
    a = Alias("a", None)
    b = Alias("b", None)
    va = Alias("va", None)
    vb = Alias("vb", None)
    m = Alias("m", None)
    
    Message = Definition("Message", Record(["type", "acc", "val"], [Set([String("vote")]), Acceptor, Values]))
    
    TypeOK = Definition("TypeOK", Conjunction([SubsetEquals(network, Alias("Message", None)), In(decided, Mapping([Acceptor],[Union(Values, Set([Scalar(-1)]))]))]))
    
    QuorumAgreedValues = Definition("QuorumAgreedValues", SetOf(v, Values, ExistentialQuantifier([Q], Subset(Acceptor), Conjunction([Cardinality(Q) >= Quorum, UniversalQuantifier([a1], Q, In(RecordInstance(["type", "acc", "val"], [String("vote"), a1, v]), network))]))))
    
    hasVoted = Definition(name = "hasVoted", arguments = [a], value = ExistentialQuantifier([v], Values, In(RecordInstance(["type", "acc", "val"], [String("vote"), a, v]), network)))
    
    voted = Definition(name="voted", arguments=[a, v], value=In(RecordInstance(["type", "acc", "val"], [String("vote"), a, v]), network))
    
    Agreement = Definition("Agreement", UniversalQuantifier([a, b], Acceptor, UniversalQuantifier([va, vb], Values, Implication(Conjunction([IndexSet(decided, a) == va, IndexSet(decided, b) == vb]), va == vb))))
    
    EnoughVotes = Definition("EnoughVotes", Cardinality(SetOf(a, Acceptor, In(RecordInstance(["type", "acc", "val"], [String("vote"), a, v]), network))) >= Quorum, [v])
    
    AllDecided = Definition("AllDecided", UniversalQuantifier([a], Acceptor, IndexSet(decided, a) == v), [v])
    
    # TODO: Add function in definitions that returns an alias
    Termination = Definition("Termination", Box(ExistentialQuantifier([v], Values, Implication(Alias("EnoughVotes", [v]), Diamond(Box(Alias("AllDecided", [v])))))))
    
    Init = Definition("Init", Conjunction([network == Set([]), decided == RecordInstance([In(a, Acceptor)], [-1])]))
    
    Send = Definition("Send", network == Union(network, Set([m])), [m])
    
    Decide = Definition("Decide", Conjunction([ExistentialQuantifier([v], Alias("QuorumAgreedValues", None), decided == SetExcept(decided, a, v)), Unchanged(network)]), [a])
    
    CastVote = Definition("CastVote", Conjunction([Not(Alias("hasVoted", [a])), Alias("Send", [(RecordInstance(["type", "acc", "val"], [String("vote"), a, v]))]), Unchanged(decided)]), arguments=[a, v])
    
    Next = Definition("Next", Disjunction([ExistentialQuantifier([a], Acceptor, ExistentialQuantifier([v], Values, Alias("CastVote", [a, v]))), ExistentialQuantifier([a], Acceptor, Alias("Decide", [a]))]))
    
    _Spec = Definition("Spec", Conjunction([Alias("Init", None), Box(FrameCondition(Alias("Next", None), [network, decided])), WeakFairness(Alias("Next", None), [network, decided])]))
                                            
    Inv = Definition("Inv", Conjunction([Alias("TypeOK", None) , Alias("Agreement", None)]))
    
    defs = [Message, TypeOK, QuorumAgreedValues, hasVoted, voted, Agreement, EnoughVotes, AllDecided, Termination, Init, Send, Decide, CastVote, Next, _Spec, Inv]
    
    # Spec
    
    spec = Spec(module="OneRoundHonestQuorum", extends=extends, constants=consts, assumptions=assumption, variables=vars, defs=defs)
    
    # Create TLA+ Spec
    
    f = open("OneRoundHonestQuorum.tla", "w")
    f.write(repr(spec))
    f.close()
    
def test_byzantine_quorum_infinite():
    """ Replicate the ByzantineQuorumInfinite specification from the repo """
        
    name="ByzantineQuorumInfinite"
    extends=["Integers", "FiniteSets"]  #TODO: Create a constant for Integers and FiniteSets (E.G Module Names or smth)
    
    Values = Constant("Values")
    Acceptors = Constant("Acceptors")
    NumberByzantineAcceptors = Constant("NumberByzantineAcceptors")
    Quorum = Constant("Quorum")
    MaxDivergence = Constant("MaxDivergence")
    
    constants=Constants([Values, Acceptors, NumberByzantineAcceptors, Quorum, MaxDivergence])
    
    assumption=Assume(
        name="QuorumAssumption",
        expr=Conjunction([
            LessThanEquals(Quorum, Cardinality(Acceptors) + NumberByzantineAcceptors),
            GreaterThan(Quorum, (Cardinality(Acceptors) + NumberByzantineAcceptors) / Scalar(2))
        ])
    )
    
    network = Variable("network")
    decided = Variable("decided")
    counters = Variable("counters")
    
    vars = Variables([network, decided, counters])
    
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
    Q = Alias("Q", None)
    
    
    # Definitions
        
    Message = Definition(
        name="Message", 
        value=Record(
            ["type", "acc", "value", "epoch"], 
            [Set([String("vote")]), Acceptors, Values, Alias("Nat", None)]) #TODO: Create a constant for Nat (E.G Module Names or smth)
    )
    

    TypeOK = Definition(
        name="TypeOK",
        value=Conjunction([
            SubsetEquals(network, Alias("Message", None)),
            In(counters, Mapping([Acceptors], [Alias("Nat", None)])),
            UniversalQuantifier(
                [a], 
                Acceptors,
                In(IndexSet(decided, a), Subset(Record(["value", "epoch"], [Union(Values, Set([Scalar(-1)])), Union(Alias("Nat", None), Set([Scalar(-1)]))])))
            )
        ])
    )
    
    QuorumAgreedValues = Definition(
        name="QuorumAgreedValues",
        arguments=[e],
        value=SetOf(
            v,
            Values,
            ExistentialQuantifier(
                variables=[Q],
                set=Subset(Acceptors),
                predicate=Conjunction([
                    ExistentialQuantifier(
                        variables=[x],
                        set=Range(Scalar(0), NumberByzantineAcceptors),
                        predicate=Cardinality(Q) >= (Quorum - x)
                    ),
                    UniversalQuantifier(
                        variables=[a1],
                        set=Q,
                        predicate=In(RecordInstance(["type", "acc", "val", "epoch"], [String("vote"), a1, v, e]) , network)
                    )
                ])
            )
        ),
    )

    counterValues = Definition(
        name="counterValues",
        value=SetFrom(
            IndexSet(
                counters,
                p),
            In(p, Acceptors)
        ),
    )

    MinCounterValue = Definition(
        name="MinCounterValue",
        value=Choose(
            c1,
            Alias("counterValues", None),
            UniversalQuantifier(
                [c2],
                Alias("counterValues", None),
                c1 <= c2,
            ),
        ),
    )

    RespectsDivergence = Definition(
        name="RespectsDivergence",
        arguments=[c],
        value=(c - Alias("MinCounterValue", None)) <= MaxDivergence,
    )

    GCDecided = Definition(
        name="GCDecided",
        arguments=[vals],
        value=Union(
                SetOf(
                    v1,
                    SetFrom(
                        RecordInstance(
                            ["epoch", "value"],
                            [Alias("v2.epoch", None) - Alias("MinCounterValue", None), Alias("v2.value", None)],
                        ),
                        In(
                            v2, vals
                        ),
                    ),
                    Alias("v1.epoch", None) >= Scalar(0),
                ),
                Set([RecordInstance(["epoch", "value"], [-1, -1])]),
            )
        )

    # Gotta fix this
    GarbageCollection = Definition(
        name="GarbageCollection",
        value=Conjunction(
            [
                Alias("MinCounterValue", None) > Scalar(0),
                Equals(
                    Alias("counters'"),
                    RecordInstance(
                        [In(p, Acceptors)],
                        [IndexSet(counters, p) - Alias("MinCounterValue", None)],
                    ),
                ),
                Equals(
                    Alias("network'"),
                    SetOf(
                        m1,
                        SetFrom(
                            RecordInstance(
                                ["type", "acc", "val", "epoch"],
                                [
                                    String("vote"),
                                    Alias("m2.acc", None),
                                    Alias("m2.val", None),
                                    Alias("m2.epoch", None) - Alias("MinCounterValue", None),
                                ],
                            ),
                            In(m2, network),
                        ),
                        Alias("m1.epoch", None) >= Scalar(0),
                    ),
                ),
                Equals(
                    Alias("decided'"),
                    RecordInstance(
                        [In(a, Alias("DOMAIN decided", None))], # TODO: Add DOMAIN operator
                        [Alias("GCDecided", [IndexSet(decided, a)])],
                    ),
                ),
            ],
        ),
    )

    BoundedDivergence = Definition(
        name="BoundedDivergence",
        value=UniversalQuantifier(
            [c],
            Alias("counterValues", None),
            Alias("RespectsDivergence", [c]),
        ),
    )

    Monotonic = Definition(
        name="Monotonic",
        value=UniversalQuantifier(
            [p],
            Acceptors,
            Alias("counters'[p]", None) >= IndexSet(counters, p), # TODO: Add primed operator for variables (e.g. a' = a -> Primed(a) == a)
        ),
    )

    Monotonicity = Definition(
        name="Monotonicity",
        value=Box(
            FrameCondition(
                Disjunction(
                    [
                        Alias("Monotonic", None),
                        UniversalQuantifier(
                            [a1, a2],
                            Acceptors,
                            Equals(
                                Alias("counters'[a1]", None) - IndexSet(counters, a1),
                                Alias("counters'[a2]", None) - IndexSet(counters, a2),
                            ),
                        ),
                    ],
                ),
                [counters]
            )
        ),
    )

    Agreement = Definition(
        name="Agreement",
        value=UniversalQuantifier(
            [a, b],
            Acceptors,
            UniversalQuantifier(
                [va, vb],
                Values,
                Implication(
                    ExistentialQuantifier(
                        [e],
                        Range(Scalar(0), IndexSet(counters, a)),
                        Conjunction(
                            [
                                In(
                                    RecordInstance(["value", "epoch"], [va, e]),
                                    IndexSet(decided, a),
                                ),
                                In(
                                    RecordInstance(["value", "epoch"], [vb, e]),
                                    IndexSet(decided, a),
                                ),
                            ],
                        ),
                    ),
                    va == vb,
                ),
            ),
        ),
    )

    EnoughVotes = Definition(
        name="EnoughVotes",
        arguments=[v, e],
        value=Cardinality(
            SetOf(
                a,
                Acceptors,
                In(
                    RecordInstance(
                        ["type", "acc", "val", "epoch"],
                        [String("vote"), a, v, e],
                    ),
                    network,
                ),
            ),
        )
        >= Quorum,
    )

    AllDecided = Definition(
        name="AllDecided",
        arguments=[v, e],
        value=UniversalQuantifier(
            [a],
            Acceptors,
            In(
                RecordInstance(["value", "epoch"], [v, e]),
                IndexSet(decided, a),
            ),
        ),
    )

    Termination = Definition(
        name="Termination",
        value=Box(
            ExistentialQuantifier(
                [v],
                Values,
                ExistentialQuantifier(
                    [e],
                    Range(Scalar(0), Alias("MaxDivergence", None)),
                    Implication(
                        Alias("EnoughVotes", [v, e]),
                        Diamond(Alias("AllDecided", [v, e])),
                    ),
                ),
            ),
        ),
    )

    hasVoted = Definition(
        name="hasVoted",
        arguments=[a, e],
        value=ExistentialQuantifier(
            [v],
            Values,
            In(
                RecordInstance(
                    ["type", "acc", "val", "epoch"],
                    [String("vote"), a, v, e],
                ),
                network,
            ),
        ),
    )

    NotDecided = Definition(
        name="NotDecided",
        arguments=[a, e],
        value=UniversalQuantifier(
            [v],
            Values,
            UniversalQuantifier(
                [ve],
                IndexSet(decided, a),
                NotEquals(
                    ve,
                    RecordInstance(["value", "epoch"], [v, e]),
                    )
            ),
        ),
    )

    Send = Definition(
        name="Send",
        arguments=[m],
        value=Equals(
            Alias("network'", None),
            Union(network, Set([m])),
        ),
    )

    Decide = Definition(
        name="Decide",
        arguments=[a, e],
        value=Conjunction(
            [
                Alias("NotDecided", [a, e]),
                ExistentialQuantifier(
                    [v],
                    Alias("QuorumAgreedValues", [e]),
                    Conjunction([
                        UniversalQuantifier(
                            [ve],
                            IndexSet(decided, a),
                            NotEquals(
                                ve,
                                RecordInstance(["value", "epoch"], [v, e]),
                            ),
                        ),
                        Equals(
                            Alias("decided'", None),
                            SetExcept(
                                decided,
                                a,
                                Union(
                                    Alias("@", None), # TODO: Create constant for @ operator, create condition that it can only exist within EXCEPT construct
                                    Set([RecordInstance(["value", "epoch"], [v, e])]),
                                ),
                            ),
                        ),
                    ]),

                ),
                Unchanged(counters),
                Unchanged(network),
            ],
        ),
    )

    CastVote = Definition(
        name="CastVote",
        arguments=[a, v],
        value=Conjunction(
            [
                Not(Enabled(Alias("GarbageCollection", None))),
                Not(Alias("hasVoted", [a, IndexSet(counters, a)])),
                Alias(
                    "Send",
                    [
                        RecordInstance(
                            ["type", "acc", "val", "epoch"],
                            [String("vote"), a, v, IndexSet(counters, a)],
                        )
                    ],
                ),
                Unchanged(decided),
                Unchanged(counters),
            ],
        ),
    )

    IncreaseEpoch = Definition(
        name="IncreaseEpoch",
        arguments=[a],
        value=Conjunction(
            [
                Not(Enabled(Alias("GarbageCollection", None))),
                ExistentialQuantifier(
                    [v],
                    Values,
                    In(
                        RecordInstance(["epoch", "value"], [IndexSet(counters, a), v]),
                        IndexSet(decided, a),
                    ),
                ),
                ExistentialQuantifier(
                    [v],
                    Values,
                    Alias("hasVoted", [a, IndexSet(counters, a)]),
                ),
                Alias("RespectsDivergence", [IndexSet(counters, a) + Scalar(1)]),
                Equals(
                    Alias("counters'", None),
                    SetExcept(
                        counters,
                        a,
                        Alias("@", None) + Scalar(1),
                    ),
                ),
                Unchanged(network),
                Unchanged(decided),
            ],
        ),
    )

    Init = Definition(
        name="Init",
        value=Conjunction(
            [
                Equals(network, Set([])),
                Equals(
                    counters,
                    RecordInstance([In(a, Acceptors)], [Scalar(0)]),
                ),
                Equals(
                    decided,
                    RecordInstance(
                        [In(a, Acceptors)],
                        [Set([RecordInstance(["epoch", "value"], [-1, -1])])],
                    ),
                ),
            ],
        ),
    )

    Next = Definition(
        name="Next",
        value=Disjunction(
            [
                Alias("GarbageCollection", None),
                ExistentialQuantifier(
                    [a],
                    Acceptors,
                    ExistentialQuantifier(
                        [v],
                        Values,
                        Alias("CastVote", [a, v]),
                    )
                ),
                ExistentialQuantifier(
                    [a],
                    Acceptors,
                    Alias("Decide", [a, IndexSet(counters, a)]),
                ),
                ExistentialQuantifier(
                    [a],
                    Acceptors,
                    Alias("IncreaseEpoch", [a]),
                ),
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
                        [network, counters, decided],
                    )
                ),
                WeakFairness(
                    Alias("Next", None),
                    [network, counters, decided],
                ),
            ],
        ),
    )

    Inv = Definition(
        name="Inv",
        value=Conjunction(
            [
                Alias("TypeOK", None),
                Alias("BoundedDivergence", None),
            ],
        ),
    )
    
    defs = [
        Message, TypeOK, QuorumAgreedValues, counterValues, MinCounterValue,
        RespectsDivergence, GCDecided, GarbageCollection, BoundedDivergence, Monotonic,
        Monotonicity, Agreement, EnoughVotes, AllDecided, Termination, hasVoted,
        NotDecided, Send, Decide, CastVote, IncreaseEpoch, Init, Next, _Spec, Inv
    ]
    spec = Spec(module=name, extends=extends, constants=constants, assumptions=assumption, variables=vars, defs=defs)
    
    # Create TLA+ Spec
    
    f = open("ByzantineQuorumInfinite.tla", "w")
    f.write(repr(spec))
    f.close()

test_header()
test_one_round_honest_quorum()
test_byzantine_quorum_infinite()
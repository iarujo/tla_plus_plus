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

def ast():
    """ Replicate the OneRoundHonestQuorum specification from the repo """
    
    Values = Constant("Values")
    Acceptor = Constant("Acceptor")
    MaxByzantineNodes = Constant("MaxByzantineNodes")
    Quorum = Constant("Quorum")
    
    network = Variable("network")
    decided = Variable("decided")
    
    extends = ["Integers", "FiniteSets"]
    consts = Constants([Values, Acceptor, MaxByzantineNodes, Quorum])
    assumption = [Assume("QuorumAssumption", Conjunction([Quorum <= Scalar(3), Quorum > (Scalar(3) / Scalar(2))]))]
    vars = Variables([network, decided])
    
    # Definitions
    
    Q = Alias("Q", None)
    a1 = Alias("a1", None)
    v = Alias("v", None)
    a = Alias("a", None)
    b = Alias("b", None)
    e = Alias("e", None)
    va = Alias("va", None)
    vb = Alias("vb", None)
    m = Alias("m", None)
    Nat = Alias("Nat", None)
    threshold = Alias("threshold", None)
    
    Message = Definition("Message", Record(["type", "acc", "value", "epoch"], [Set([String("vote")]), Acceptor, Values, Nat]))
    
    TypeOK = Definition("TypeOK", Conjunction([SubsetEquals(network, Alias("Message", None)), In(decided, Mapping([Acceptor],[Subset(Record(["value", "epoch"], [Union(Values, Set([Scalar(-1)])), Union(Nat, Set([Scalar(-1)]))]))]))]))
    
    EpochDef = Definition(
        "Epoch",
        Range(Scalar(0), Scalar(1)),
    )
    
    Epoch = Alias("Epoch", None)
    
    QuorumAgreedValues = Definition("QuorumAgreedValues", SetOf(v, Values, ExistentialQuantifier([Q], Subset(Acceptor), Conjunction([ByzantineComparison(Cardinality(Q), GreaterThanEquals, threshold, True, [["QuorumAgreedValues", "Decide", "Next"]]), UniversalQuantifier([a1], Q, In(RecordInstance(["type", "acc", "value", "epoch"], [String("vote"), a1, v, e]), network))]))), [e, threshold])
    
    hasVoted = Definition(name = "hasVoted", arguments = [a, e], value = ExistentialQuantifier([v], Values, In(RecordInstance(["type", "acc", "value", "epoch"], [String("vote"), a, v, e]), network)))
    
    voted = Definition(name="voted", arguments=[a, v, e], value=In(RecordInstance(["type", "acc", "value", "epoch"], [String("vote"), a, v, e]), network))
    
    Agreement = Definition("Agreement", UniversalQuantifier([a, b], Acceptor, UniversalQuantifier([va, vb], Values, UniversalQuantifier([e], Epoch, Implication(Conjunction([In(RecordInstance(["value", "epoch"], [va, e]),IndexSet(decided, a)), In(RecordInstance(["value", "epoch"], [vb, e]),IndexSet(decided, b))]), va == vb)))))
    
    EnoughVotes = Definition(
        "EnoughVotes", 
        ByzantineComparison(
            Cardinality(SetOf(a, Acceptor, In(RecordInstance(["type", "acc", "value", "epoch"], [String("vote"), a, v, e]), network))),
            GreaterThanEquals,
            Quorum,
            False,
            None
        ),
        [v, e]
    )
    
    AllDecided = Definition("AllDecided", UniversalQuantifier([a], Acceptor, In(RecordInstance(["value", "epoch"], [v, e]), IndexSet(decided, a))), [v, e])
    
    # TODO: BYZANTINE COMPARISON HERE
    Termination = Definition("Termination", Box(ExistentialQuantifier([v], Values, ExistentialQuantifier([e], Epoch, Implication(Alias("EnoughVotes", [v, e]), Diamond(Box(Alias("AllDecided", [v, e]))))))))
    
    Init = Definition("Init", Conjunction([network == Set([]), decided == RecordInstance([In(a, Acceptor)], [Set([RecordInstance(["epoch", "value"], [Scalar(-1), Scalar(-1)])])])]))
    
    Send = Definition("Send", Alias("network'", None) == Union(network, Set([m])), [m])
    
    Decide = Definition("Decide", Conjunction([ExistentialQuantifier([e], Epoch, ExistentialQuantifier([v], Alias("QuorumAgreedValues", [e, Quorum]), Alias("decided'", None) == SetExcept(decided, a, Union(Alias("@", None), Set([RecordInstance(["value", "epoch"], [v, e])]))))), Unchanged(network)]), [a])
    
    CastVote = Definition("CastVote", Conjunction([Not(Alias("hasVoted", [a, e])), Alias("Send", [(RecordInstance(["type", "acc", "value", "epoch"], [String("vote"), a, v, e]))]), Unchanged(decided)]), arguments=[a, v, e])
    
    Next = Definition("Next", Disjunction([ExistentialQuantifier([a], Acceptor, ExistentialQuantifier([v], Values, ExistentialQuantifier([e], Epoch, Alias("CastVote", [a, v, e])))), ExistentialQuantifier([a], Acceptor, Alias("Decide", [a]))]))
    
    _Spec = Definition("Spec", Conjunction([Alias("Init", None), Box(FrameCondition(Alias("Next", None), [network, decided])), WeakFairness(Alias("Next", None), [network, decided])]))
                                            
    Inv = Definition("Inv", Conjunction([Alias("TypeOK", None)])) # , Alias("Agreement", None)]))
    
    defs = [Message, TypeOK, EpochDef, QuorumAgreedValues, hasVoted, voted, Agreement, EnoughVotes, AllDecided, Termination, Init, Send, Decide, CastVote, Next, _Spec, Inv]
    
    # Spec
    
    spec = Spec(module="OneRoundHonestQuorum", extends=extends, constants=consts, assumptions=assumption, variables=vars, defs=defs)
    
    return spec
    
print(ast())

print(ast().compile())
from spec import Spec
from variables import Variables
from constants import Constants
from assume import Assume
from definition import Definition
from definition import Definition
from clause import Conjunction, Disjunction, Implication
from predicates import TRUE, FALSE, UniversalQuantifier, ExistentialQuantifier, Not, In, SubsetEquals, Equals, NotEquals, LessThan, LessThanEquals, GreaterThan, GreaterThanEquals
from terms import Constant, Variable, Scalar, Alias, Record, RecordInstance, Mapping, Unchanged, Subset, Set, SetOf, SetExcept, IndexSet, Cardinality, Addition, Substraction, Multiplication, Division, Union, Intersection
from temporal import Box, Diamond, FrameCondition, WeakFairness

def test_header01():
    extends = ["Integers", "FiniteSets"]
    consts = Constants([Constant("Values"), Constant("Acceptor"), Constant("Quorum")])
    vars = Variables([Variable("network"), Variable("decided")])
    
    spec = Spec(module="MySpec", extends=extends, constants=consts, assumptions=None, variables=vars, defs=[])
    
    print(repr(spec))
    
def test_spec01():
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
    
    Message = Definition("Message", Record(["type", "acc", "value"], ['{"vote"}', "Acceptor", "Values"])) # TODO: records still need polishing
    
    TypeOK = Definition("TypeOK", Conjunction([SubsetEquals(network, Alias("Message", None)), In(decided, Mapping(["Acceptor"],["Values \\cup {-1}"]))])) # TODO: mappings still need polishing
    
    QuorumAgreedValues = Definition("QuorumAgreedValues", SetOf(v, Values, ExistentialQuantifier([Q], Subset(Acceptor), Conjunction([Cardinality(Q) >= Quorum, UniversalQuantifier([a1], Q, In(RecordInstance(["type", "acc", "val"], [Alias('"vote"', None), a1, v]), network))]))))
    
    hasVoted = Definition(name = "hasVoted", arguments = [a], value = ExistentialQuantifier([v], Values, In(RecordInstance(["type", "acc", "val"], [Alias('"vote"', None), a, v]), network)))
    
    voted = Definition(name="voted", arguments=[a, v], value=In(RecordInstance(["type", "acc", "val"], [Alias('"vote"', None), a, v]), network))
    
    Agreement = Definition("Agreement", UniversalQuantifier([a, b], Acceptor, UniversalQuantifier([va, vb], Values, Implication(Conjunction([IndexSet(decided, a) == va, IndexSet(decided, b) == vb]), va == vb))))
    
    EnoughVotes = Definition("EnoughVotes", Cardinality(SetOf(a, Acceptor, In(RecordInstance(["type", "acc", "val"], [Alias('"vote"', None), a, v]), network))) >= Quorum, [v])
    
    AllDecided = Definition("AllDecided", UniversalQuantifier([a], Acceptor, IndexSet(decided, a) == v), [v])
    
    # TODO: Add function in definitions that returns an alias
    Termination = Definition("Termination", Box(ExistentialQuantifier([v], Values, Implication(Alias("EnoughVotes", [v]), Diamond(Box(Alias("AllDecided", [v])))))))
    
    Init = Definition("Init", Conjunction([network == Set([]), decided == RecordInstance([In(a, Acceptor)], [-1])]))
    
    Send = Definition("Send", Alias("network'", None) == Union(network, Set([m])), [m])
    
    Decide = Definition("Decide", Conjunction([ExistentialQuantifier([v], Alias("QuorumAgreedValues", None), Alias("decided'", None) == SetExcept(decided, a, v)), Unchanged(network)]), [a])
    
    CastVote = Definition("CastVote", Conjunction([Not(Alias("hasVoted", [a])), Alias("Send", [(RecordInstance(["type", "acc", "val"], [Alias('"vote"', None), a, v]))]), Unchanged(decided)]), arguments=[a, v])
    
    Next = Definition("Next", Disjunction([ExistentialQuantifier([a], Acceptor, ExistentialQuantifier([v], Values, Alias("CastVote", [a, v]))), ExistentialQuantifier([a], Acceptor, Alias("Decide", [a]))]))
    
    _Spec = Definition("Spec", Conjunction([Alias("Init", None), Box(FrameCondition(Alias("Next", None), [network, decided])), WeakFairness(Alias("Next", None), [network, decided])]))
                                            
    Inv = Definition("Inv", Conjunction([Alias("TypeOK", None) , Alias("Agreement", None)]))
    
    defs = [Message, TypeOK, QuorumAgreedValues, hasVoted, voted, Agreement, EnoughVotes, AllDecided, Termination, Init, Send, Decide, CastVote, Next, _Spec, Inv]
    
    # Spec
    
    spec = Spec(module="OneRoundHonestQuorum", extends=extends, constants=consts, assumptions=assumption, variables=vars, defs=defs)
    
    # Create TLA+ Spec
    
    # Must fix:
    # 'vote' -> "vote"
    # 
    
    f = open("OneRoundHonestQuorum.tla", "w")
    f.write(repr(spec))
    f.close()
    
test_spec01()
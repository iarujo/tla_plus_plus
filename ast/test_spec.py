from spec import Spec
from variables import Variables
from constants import Constants
from assume import Assume
from definition import Definition
from definition import Definition
from alias import Alias
from clause import Conjunction, Disjunction, Implication
from predicates import TRUE, FALSE, UniversalQuantifier, ExistentialQuantifier, Not, Equals, NotEquals, LessThan, LessThanEquals, GreaterThan, GreaterThanEquals
from terms import Constant, Variable, Scalar, Record, RecordInstance, Function, Addition, Substraction, Multiplication, Division, Union, Intersection

def test_header01():
    extends = ["Integers", "FiniteSets"]
    consts = Constants([Constant("Values"), Constant("Acceptor"), Constant("Quorum")])
    vars = Variables([Variable("network"), Variable("decided")])
    
    spec = Spec(module="MySpec", extends=extends, constants=consts, assumptions=None, variables=vars, defs=[])
    
    print(repr(spec))
    
def test_spec01():
    
    Values = Constant("Values")
    Acceptor = Constant("Acceptor")
    Quorum = Constant("Quorum")
    
    extends = ["Integers", "FiniteSets"]
    consts = Constants([Values, Acceptor, Quorum])
    assumption = Assume("QuorumAssumption", Conjunction([Quorum <= Scalar(3), Quorum > (Scalar(3) / Scalar(2))])) # TODO: Add Cardinality Function
    vars = Variables([Variable("network"), Variable("decided")])
    
    Message = Definition("Message", Record(["type", "acc", "value"], ["{'vote'}", "Acceptor", "Values"])) # TODO: records still need polishing
    
    defs = [Message]
    
    spec = Spec(module="MySpec", extends=extends, constants=consts, assumptions=assumption, variables=vars, defs=defs)
    
    print(repr(spec))
    
test_spec01()
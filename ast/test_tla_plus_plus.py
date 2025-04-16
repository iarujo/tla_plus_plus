from src.spec import Spec
from src.variables.variables import Variables
from src.constants.constants import Constants
from src.assume.assume import Assume
from src.definitions.definition import Definition
from src.definitions.clause.clause import Conjunction, Disjunction, Implication
from src.definitions.predicates.predicates import ArithmeticComparison, TRUE, FALSE, UniversalQuantifier, ExistentialQuantifier, Not, In, SubsetEquals, Equals, NotEquals, LessThan, LessThanEquals, GreaterThan, GreaterThanEquals
from src.definitions.terms.terms import Constant, Variable, Scalar, String, Alias, Unchanged, Enabled, Choose, Range, Addition, Substraction, Multiplication, Division
from src.definitions.terms.records import Record, RecordInstance, Mapping
from src.definitions.terms.finiteSet import Subset, Set, SetOf, SetFrom, SetExcept, IndexSet, Cardinality, Union, Intersection
from src.definitions.temporal import Box, Diamond, FrameCondition, WeakFairness
from src.tla_plusplus.tla_plusplus_byzantine import ByzantineComparison

def test_print_byzantine_comparison(comp: ArithmeticComparison):
    """ Ensure a simple spec with a byzantine comparison is created correctly """
    
    extends = ["Integers"]
    consts = Constants([Constant("MaxByzantineNodes")])
    
    comparison = Definition(
        name="comparison",
        value=ByzantineComparison(
            variable=Variable("comparison"),
            comparison=comp,
            threshold=Variable("MaxByzantineNodes")
        )
    )
    
    spec = Spec(module="MySpec", extends=extends, constants=consts, assumptions=None, variables=None, defs=[comparison])
    
    print(repr(spec))
    
def test_print_byzantine_comparison_all():
    """ Test all arithmetic comparisons """
    
    comparisons = [
        Equals,
        NotEquals,
        LessThan,
        LessThanEquals,
        GreaterThan,
        GreaterThanEquals
    ]
    
    for comparison in comparisons:
        test_print_byzantine_comparison(comparison)
        
def test_compile_byzantine_comparison(comp: ArithmeticComparison):
    
    extends = ["Integers"]
    consts = Constants([Constant("MaxByzantineNodes")])
    
    comparison = Definition(
        name="comparison",
        value=ByzantineComparison(
            variable=Variable("comparison"),
            comparison=comp,
            threshold=Variable("MaxByzantineNodes")
        )
    )
    
    spec = Spec(module="MySpec", extends=extends, constants=consts, assumptions=None, variables=None, defs=[comparison])
            
    compiled = spec.compile()
    
    print(f'TLA++ Spec: \n\n {repr(spec)} \n\nTLA+ Spec: \n\n {repr(compiled)}')
    
def test_compile_byzantine_invalid_spec_fails(comp: ArithmeticComparison):
    
    extends = ["Integers"]
    consts = Constants([Constant("ThisAintMaxByzantineNodes")])
    
    comparison = Definition(
        name="comparison",
        value=ByzantineComparison(
            variable=Variable("comparison"),
            comparison=comp,
            threshold=Variable("ThisAintMaxByzantineNodes")
        )
    )
    
    spec = Spec(module="MySpec", extends=extends, constants=consts, assumptions=None, variables=None, defs=[comparison])
            
    compiled = spec.compile()
    
    # Make sure this throws an error:
    # print(repr(compiled))
    
    
        
test_compile_byzantine_comparison(Equals)
#test_compile_byzantine_invalid_spec_fails(Equals)
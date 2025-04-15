from typing import List
from src.definitions.terms.terms import Term

class TemporalOperator():
    """
    Base class for all temporal terms
    """
    
    def __init__(self):
        pass
    
    def compile(self, spec):
        """
        Transforms the term into a valid TLA+ term.
        """
        raise NotImplementedError("This method should be implemented in subclasses.")
    
class Box(TemporalOperator):
    """
    The box operator []A, which means "A holds in all states of the system"
    """
    
    def __init__(self, term: Term):
        self.term = term
        
    def __repr__(self):
        return f"[]{self.term}"
    
    def compile(self, spec):
        return Box(self.term.compile(spec))
    
class Diamond(TemporalOperator):
    """
    The diamond operator <>A, which means "A holds in some state of the system"
    """
    
    def __init__(self, term: Term):
        self.term = term
        
    def __repr__(self):
        return f"<>{self.term}"
    
    def compile(self, spec):
        return Diamond(self.term.compile(spec))
    
class FrameCondition(TemporalOperator):
    """
    Action with a Frame Condition on Primed Variables
    """
    
    def __init__(self, action: Term, variables: List[Term]):
        self.action = action
        self.variables = variables
        
    def __repr__(self):
        return f"[{self.action}]_<<{', '.join(repr(v) for v in self.variables)}>>"
    
    def compile(self, spec):
        return FrameCondition(self.action.compile(spec), [v.compile(spec) for v in self.variables])
    
class WeakFairness(TemporalOperator):
    """
    Action with a Frame Condition on Primed Variables
    """
    
    def __init__(self, action: Term, variables: List[Term]):
        self.action = action
        self.variables = variables
        
    def __repr__(self):
        return f"WF_<<{', '.join(repr(v) for v in self.variables)}>>({self.action})"
    
    def compile(self, spec):
        return WeakFairness(self.action.compile(spec), [v.compile(spec) for v in self.variables])
from typing import List
from terms import Term

class TemporalOperator():
    """
    Base class for all temporal terms
    """
    
    def __init__(self):
        pass
    
class Box(TemporalOperator):
    """
    The box operator []A, which means "A holds in all states of the system"
    """
    
    def __init__(self, term: Term):
        self.term = term
        
    def __repr__(self):
        return f"[]{self.term}"
    
class Diamond(TemporalOperator):
    """
    The diamond operator <>A, which means "A holds in some state of the system"
    """
    
    def __init__(self, term: Term):
        self.term = term
        
    def __repr__(self):
        return f"<>{self.term}"
    
class FrameCondition(TemporalOperator):
    """
    Action with a Frame Condition on Primed Variables
    """
    
    def __init__(self, action: Term, variables: List[Term]):
        self.action = action
        self.variables = variables
        
    def __repr__(self):
        return f"[{self.action}]_<<{', '.join(repr(v) for v in self.variables)}>>"
    
class WeakFairness(TemporalOperator):
    """
    Action with a Frame Condition on Primed Variables
    """
    
    def __init__(self, action: Term, variables: List[Term]):
        self.action = action
        self.variables = variables
        
    def __repr__(self):
        return f"WF_<<{', '.join(repr(v) for v in self.variables)}>>({self.action})"
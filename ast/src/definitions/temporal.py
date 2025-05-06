from typing import List
from src.definitions.terms.terms import Term

class TemporalOperator():
    """
    Base class for all temporal terms
    """
    
    def __init__(self):
        pass
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        raise NotImplementedError("This method should be implemented in subclasses.")
    
    def compile(self, spec):
        """
        Transforms the term into a valid TLA+ term.
        """
        raise NotImplementedError("This method should be implemented in subclasses.")
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return False
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the predicate to a new one.
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
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.term.preCompile(spec)
    
    def compile(self, spec):
        return Box(self.term.compile(spec))
    
    def byzComparisonToNormal(self, spec):
        return Box(self.term.byzComparisonToNormal(spec))
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return self.term.isByzComparison()
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the temporal predicate to a new one.
        """
        self.term.changeAliasTo(old, new)
    
class Diamond(TemporalOperator):
    """
    The diamond operator <>A, which means "A holds in some state of the system"
    """
    
    def __init__(self, term: Term):
        self.term = term
        
    def __repr__(self):
        return f"<>{self.term}"
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.term.preCompile(spec)
    
    def compile(self, spec):
        return Diamond(self.term.compile(spec))
    
    def byzComparisonToNormal(self, spec):
        return Diamond(self.term.byzComparisonToNormal(spec))
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return self.term.isByzComparison()
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the temporal predicate to a new one.
        """
        self.term.changeAliasTo(old, new)
    
class FrameCondition(TemporalOperator):
    """
    Action with a Frame Condition on Primed Variables
    """
    
    def __init__(self, action: Term, variables: List[Term]):
        self.action = action
        self.variables = variables
        
    def __repr__(self):
        return f"[{self.action}]_<<{', '.join(repr(v) for v in self.variables)}>>"
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        self.action.preCompile(spec)
        for v in self.variables:
            v.preCompile(spec)
    
    def compile(self, spec):
        return FrameCondition(self.action.compile(spec), [v.compile(spec) for v in self.variables])
    
    def byzComparisonToNormal(self, spec):
        return FrameCondition(self.action.byzComparisonToNormal(spec), [v.byzComparisonToNormal(spec) for v in self.variables])
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return self.action.isByzComparison() or any(v.isByzComparison() for v in self.variables)
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the temporal predicate to a new one.
        """
        self.action.changeAliasTo(old, new)
        for v in self.variables:
            v.changeAliasTo(old, new)
            
class WeakFairness(TemporalOperator):
    """
    Action with a Frame Condition on Primed Variables
    """
    
    def __init__(self, action: Term, variables: List[Term]):
        self.action = action
        self.variables = variables
        
    def __repr__(self):
        return f"WF_<<{', '.join(repr(v) for v in self.variables)}>>({self.action})"
    
    def set_action(self, action: Term):
        """
        Set the action of the WeakFairness term.
        """
        self.action = action
    
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        pass
    
    def compile(self, spec):
        return self
    
    def byzComparisonToNormal(self, spec):
        return WeakFairness(self.action.byzComparisonToNormal(spec), [v.byzComparisonToNormal(spec) for v in self.variables])
    
    def isByzComparison(self):
        """
        Returns True if the term is a Byzantine comparison, False otherwise.
        """
        return self.action.isByzComparison() or any(v.isByzComparison() for v in self.variables)
    
    def changeAliasTo(self, old: str, new: str):
        """
        Change an alias inside the temporal predicate to a new one.
        """
        self.action.changeAliasTo(old, new)
        for v in self.variables:
            v.changeAliasTo(old, new)
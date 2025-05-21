from abc import ABC, abstractmethod

class AbstractTerm(ABC):
    
    def __init__(self):
        pass

    @abstractmethod
    def __repr__(self):
        pass
    
    @abstractmethod
    def get_node_count(self):
        """
        Return the number of nodes in the term.
        """
        pass
    
    @abstractmethod
    def preCompile(self, spec):
        """
        Pre-compilation applies changes to the spec without necessarily returning new objects
        """
        pass

    @abstractmethod
    def compile(self, spec):
        """
        Compile the term into a valid TLA+ expression.
        """
        pass
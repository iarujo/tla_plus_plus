from abc import ABC, abstractmethod

class AbstractTerm(ABC):
    
    def __init__(self):
        pass

    @abstractmethod
    def __repr__(self):
        pass

    @abstractmethod
    def compile(self, spec):
        """
        Compile the term into a valid TLA+ expression.
        """
        pass
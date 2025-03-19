from abc import ABC, abstractmethod

class AbstractTerm(ABC):
    
    def __init__(self):
        pass

    @abstractmethod
    def __repr__(self):
        pass

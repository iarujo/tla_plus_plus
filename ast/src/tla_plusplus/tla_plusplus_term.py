from src.definitions.terms.terms import Term

class TLAPlusPlusTerm(Term):
    """
    Abstract class for all terms of our extension to TLA+.
    """
    
    def __init__(self):
        super().__init__()
    
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
    
    
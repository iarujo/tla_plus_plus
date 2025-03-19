from typing import List, Optional

class Alias():
    """Term representing an alias for a definition that must be declared elsewhere in the AST."""
    # Note: some aliases return boolean values, while others just return a value of any other kind. Should we make a distinction between these?

    def __init__(
            self,
            name: str,
            arguments: Optional[List[str]] = None):
        
        self.name = name
        if arguments is None:
            self.arguments = []
        else:
            self.arguments = arguments

    def __repr__(self):
        if(self.arguments):
            return f"{self.name}({', '.join(repr(a) for a in self.arguments)})"
        return f"{self.name}"
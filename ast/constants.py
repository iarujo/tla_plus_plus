from typing import List
from terms import Constant

class Constants:
    
    def __init__(self, constants: List[Constant]):
        self.constants = constants
        
    def __repr__(self):
        return f"CONSTANTS {', '.join(repr(v) for v in self.constants)}"
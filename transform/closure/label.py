from id import Id

class Label:
    def __init__(self, label: Id):
        self.label = label
        self.loc = -1
    
    def __repr__(self) -> str:
        return f'[label:{self.label}@{hex(id(self))}]'
    
    def __str__(self) -> str:
        return str(self.label)
class BasicBlock:
    """Represents a basic block of a program."""
    def __init__(self, data: dict):
        assert "start_pc" in data, "basic block has no start_pc"
        assert "statements" in data, "basic block has no statements"
        self.start_pc = data["start_pc"]
        self.statements = data["statements"]

    def __eq__(self, other: 'BasicBlock') -> bool:
        return self.start_pc == other.start_pc and self.statements == other.statements

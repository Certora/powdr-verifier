class BasicBlock:
    """Represents a basic block of a program."""

    def __init__(self, data: dict):
        """Initialize the basic block from a JSON-like dict."""
        assert "start_pc" in data, "basic block has no start_pc"
        assert "statements" in data, "basic block has no statements"
        self.start_pc = data["start_pc"]
        assert self.start_pc == 0
        self.statements = data["statements"]

    def __eq__(self, other: "BasicBlock") -> bool:
        """Return True iff both blocks have the same `start_pc` and `statements`."""
        return self.start_pc == other.start_pc and self.statements == other.statements

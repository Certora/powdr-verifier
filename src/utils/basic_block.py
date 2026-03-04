class BasicBlock:
    """Represents a basic block of a program."""

    def __init__(self, data: dict):
        """Initialize the basic block from a JSON-like dict."""
        if "blocks" in data:
            assert len(data["blocks"]) == 1, "basic block has multiple blocks"
            data = data["blocks"][0]
        assert "start_pc" in data, "basic block has no start_pc"
        assert "instructions" in data, "basic block has no instructions"
        self.start_pc = data["start_pc"]
        assert self.start_pc == 0
        self.instructions = data["instructions"]

    def __eq__(self, other: "BasicBlock") -> bool:
        """Return True iff both blocks have the same `start_pc` and `instructions`."""
        return self.start_pc == other.start_pc and self.instructions == other.instructions

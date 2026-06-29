"""membus — examine, extract, and align memory-bus interactions across circuits.

A lens-style CLI over powdr APC dumps, focused on the memory bus (id 1). It
reuses `src/lens/` for auto-discovery, loading, normalization, and output
conventions, and productizes the busat `tools/` prototypes (timestamp-order
deduction, key recovery, abstract-order extraction).
"""

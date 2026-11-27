# Reducing an extracted instruction

Use [Bytecode](Bytecode.lean) for equations about instruction classifiers and [Interp](Interp.lean) for interpreter dispatch. These equations let a proof select an instruction family without splitting the full bytecode enumeration. Compiler proofs can import the bytecode equations independently.

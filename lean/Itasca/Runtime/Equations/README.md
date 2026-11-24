# Equations for extracted operations

These modules expose selected defining equations from narrow extracted runtime
partitions. Instruction-family proofs use them to avoid repeatedly splitting the
entire bytecode enumeration or depending on incidental generated match names.

[Bytecode](Bytecode.lean) provides bytecode equations and [Interp](Interp.lean)
interpreter equations. Import the smallest equation owner needed by a consumer;
compiler proofs must not gain interpreter-function dependencies through an
equation aggregator. Generated declarations remain regenerated from Rust, never
edited here.

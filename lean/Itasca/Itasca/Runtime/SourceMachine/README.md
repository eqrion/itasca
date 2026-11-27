# A flat machine for the source semantics

The [flat state and its decoding](Definitions.lean) represent frames and labels explicitly and reconstruct SpecTec evaluation contexts. This gives the interpreter proof a source state it can relate to a concrete stack at each step. Simulation carries those steps back to the host-aware reduction relation `WebAssembly.StepsH` used in the public execution theorems.

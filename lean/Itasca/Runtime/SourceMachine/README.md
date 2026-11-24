# Independent flat source machine

The source machine represents specification values/instructions with flat frames
and labels. Its decode reconstructs SpecTec evaluation contexts. Transition,
typing, ownership, supported-instruction and simulation proofs connect this
representation to the host-aware source relation `SpecExt.StepsH`.

The flat state and decoding definitions live in [Definitions](Definitions.lean).
They are simulation tools, not part of the public audit vocabulary. Public
execution statements use SpecTec configurations and SpecExt reductions directly.
Internal resource adequacy proofs quantify over source states and permitted host
replies; their capacity premises are not public API obligations.

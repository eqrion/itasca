# Runtime specification lemmas

This layer proves source-only facts about generated typing, numeric and SIMD
operations, memory growth, segment initialization and module membership. It
supports representation, source-machine and execution proofs without depending
on the extracted runtime implementation.

Public definitions used by theorem statements live in narrow
[Interface specification owners](../../Results/Definitions/README.md). Generated
judgments and patched builtins remain named foundations. Preserve that separation:
facts about source typing cannot assume that a compiler or interpreter succeeded.

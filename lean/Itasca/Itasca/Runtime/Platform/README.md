# Witnesses for platform laws

[VecMemory](VecMemory.lean) proves the memory laws for the extracted vector implementation under allocator correctness. [FloatWitness](FloatWitness.lean) constructs a mathematical float implementation by selecting results permitted by the specification. Native arithmetic, allocation, and host callbacks carry their own obligations at the [execution boundary](../../../../README.md#execution-boundary).

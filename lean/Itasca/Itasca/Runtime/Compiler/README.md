# From source syntax to slot code

The compiler proof builds a syntactic correspondence in three stages. [Local](Local/README.md) accounts for one callback’s emissions and state changes. [Body](Body/README.md) joins those effects across structured control flow. [Module](Module/README.md) collects compiled entries and initializers in source order. Dependencies follow that order, and all three stages stay independent of interpreter operations. The resulting [public certificate](../../Results/Definitions/Compiler/Compilation.lean) can then be used by execution proofs.

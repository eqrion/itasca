# Typing-rule support

[DeclaredReferences](Typing.lean) proves the declared-reference facts needed alongside the
generated typing judgments. [Typing](Typing.lean) decomposes
typing derivations for instruction and completeness proofs. These lemmas concern
the declarative specification, independently of validator acceptance.

The public declared-reference vocabulary lives in
[Results/Definitions/Spec/DeclaredReferences](../Results/Definitions/Binary.lean#L614).
The generated specification omits the additional `ref.func` declaration condition;
the validator certificate retains it explicitly. This foundation cannot import
higher validator or runtime implementation layers.

# Module parsing and assembly

These proofs connect extracted section readers and metadata to the independent
raw-module grammar and generated typing judgments. Environment parsing builds
index-space caches; code framing separates entries and locals; tail parsing
handles the declarations after code. Elaboration connects raw syntax to SpecTec.

[Layout](Layout.lean) assembles environment, entry and tail certificates into
the accepted-module certificate. Its public meaning is defined in
[public-definition module layout](../Results/Definitions/Validation.lean#L1333).
Independent encoding, elaboration, restrictions and returned accessor types must
all describe the same raw module.

Module proofs use body/entry certificates and foundations. Stream consumes the
assembled regions. Runtime may consume validation results. Validation depends
on validator functions and remains independent of runtime implementation proofs.

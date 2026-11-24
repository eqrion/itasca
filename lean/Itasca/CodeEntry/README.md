# Function entries and validation contracts

[Encoding](Encoding.lean) connects size prefixes, local declarations and body
bytes to the environment's function type and the unified body certificate.
[Signature limits](../Results/Definitions/Validation.lean#L656) are shared by
decoder contracts and completeness premises. [Validation](Validation.lean) proves callback/plain-validation
correspondence, entry acceptance and encoding uniqueness;
[Trace](Trace.lean) connects accepted entry execution to body observations.

Public entry encoding, typing and limit vocabulary is defined under
[Results/Definitions/CodeEntry](../Results/Definitions/README.md).
The name describes a binary code-section entry; no runtime profile selection is
modeled. Module and streaming proofs compose these entry certificates. Entry
offsets refer to the entire code region; positions within a body are relative to
that instruction body.

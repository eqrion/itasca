# Independent binary grammar proofs

This layer proves properties of the byte grammar and its primitive readers:
unsigned/signed LEB128, names and UTF-8, instruction immediates, instruction
sequences and module framing. The grammar relates bytes to syntax independently
of whether the validator accepts them. Nonminimal permitted LEB encodings and raw
floating-point/vector bits remain represented.

Public grammar definitions are under
[Results/Definitions/Binary](../Results/Definitions/README.md). The files here
prove decoding, encoding and uniqueness properties. Module consumers use these
properties to connect exact input bytes to declarative typing; traces use
uniqueness to identify instruction trees independently obtained from the same bytes.

Imports remain within the foundation and narrow public definitions. This
layer must not acquire body-validation, module-driver or runtime dependencies.

# Concrete/source representation proofs

[Values](Values.lean), [Layout](Layout.lean) and
[Store](Store.lean) prove slot-value, layout, decoding and capacity
facts shared by compiler, store and interpreter constructions. Their public
semantic definitions are under
[Interface representation](../../Results/Definitions/README.md).

`Representation.CodeInterpretation` supplies source bodies for compiled functions;
`decodeStore` uses it to decode retained concrete objects. Neither assumes machine
execution correctness. Keep capacities and representation below the compiler
that constructs them and the interpreter that consumes them, avoiding a compiler
dependency on extracted interpreter functions.

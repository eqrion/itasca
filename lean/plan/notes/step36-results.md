# Step 3.6 results

Completed 2026-11-13. StoreCreate now provides monotonicity lemmas for
ExternalIssued, IssuedValue, and ValueInStore under unchanged store identity
and growth of the relevant address vectors. These cover external-identity
appends as well as ordinary object growth. Three derived lemmas for StagedPrefix
and three for CumulativeStoreMutation transport the same handle/value facts
through the relations returned by the store API contracts.

The proofs use retained list lengths, metadata equality, and decoded source
extension. They do not inspect any operation implementation. LSP, targeted
checks, cached integration (4,064 jobs), lint, links, and audit pass. Direct
axiom checks of all six relation-specific lemmas report only standard logical
axioms, with no source-scan warnings. The headline audit is unchanged. No metric
ratchet worsened, imports or modules were added, resource limits increased, or
trust boundaries changed. The change adds 108 handwritten lines. Rust and
extracted definitions were unchanged.

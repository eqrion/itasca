# Step 3.5 results

Completed 2026-11-13. StoreRead provides total contracts for global, memory,
table size/element, function type, external identity, and export lookup under
the required issued-handle and platform premises. Successful global and table
reads also return ValueInStore, so callers can compose them with writes.

Reads identify the relevant decoded objects and values. External identities
correspond to the raw identity vector, which the source store does not contain.
Export lookup corresponds to the decoded instance exports; instances likewise
are not a source-store field. The export contract identifies the first matching
raw byte name, characterizes missing results, and proves issuance and source
address correspondence. It handles arbitrary byte queries without assuming
UTF-8 validity or injectivity of name decoding on invalid inputs.

Store/Api/Exports proves the byte comparison and export-search loops and their
lookup bridges. Two small helpers in existing unfolding modules expose the
compiler environment accessor and foreign function-type rejection, avoiding
additional unfolding sites for existing functions. Compiler import isolation
is preserved.

LSP, targeted checks, cached integration (4,064 jobs), lint, links, and audit
pass. Direct checks of all seven public contracts and the two shared helpers
report only the three standard logical axioms, with no source-scan warnings.
The headline audit is byte-for-byte unchanged. No metric ratchet worsened or
resource limit increased. There are 784 handwritten modules and 528 added proof
lines. No trust boundary changed; Rust and extracted definitions were unchanged.

# Step 3.1 results

Completed 2026-11-13. Shared vector lookup and mutation equalities now live
beside vec_index_given in Interp/Relations/Defaults. The identical private pairs
in GlobalCoreStep and TableSource were removed and their callers use the public
lemmas.

MemoryGrowth.extends and TableGrowth.extends now derive source-store extension
from the existing raw growth effects, shape, syntax, and issued-index premises
(and an owned table initializer). They use lower-layer decoding/specification
lemmas, without importing integration proofs into Store.

Integration/Api/StoreCreate adds Shape.of_allocated and
ExecutableInv.append_hosts. The latter preserves the executable invariant and
extends the decoded store under retained-prefix, shape, unchanged instance/
segment, and host-only addition premises. Statements match the planned contracts.

LSP checks, targeted builds, full integration (4,059 jobs), lint, links, and
diff checks pass. The headline audit is byte-for-byte unchanged. All four new
growth/construction helper axioms were also checked directly: only propext,
Classical.choice, and Quot.sound, with no source-scan warnings. No limits were
raised, no metric ratchet worsened, and no trust boundary changed. Rust and
extracted definitions were unchanged, so no regeneration was needed.

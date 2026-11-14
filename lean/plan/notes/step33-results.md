# Step 3.3 results

Completed 2026-11-13. StoreDefine provides contracts for external references,
hosts, memories, tables, and globals, in that order. All preserve the executable
invariant and leave the exact store unchanged on failure. Success establishes
issued handles and the requested host signature, memory buffer, null table
contents, or decoded global value. Global definitions require issued values
and cover ownership and type rejection as well as allocation failure.

The host contract proves the atomicity introduced in step 3.0: a newly interned
signature and its function fit the two-object capacity check. External-reference
and host append helpers transport the executable invariant. Memory, table, and
global contracts reuse the existing raw effects; a small rejection helper in
DefineTable covers the missing global rejection paths without another unfolding
module or a higher-layer import.

LSP checks, targeted builds, cached integration (4,060 jobs), lint, links, and
audit pass. Each of the five public contracts and the new rejection helper was
also checked directly: only the three standard logical axioms, with no source
scan warnings. The headline audit is byte-for-byte unchanged. No metric ratchet
worsened; the new API module brings the handwritten module count to 780, with
552 additional lines across the two proof files. No resource limits or trust
boundaries changed. Rust and extracted definitions were unchanged.

The user authorized continuing past the scalar-bound repair stop in the extern
proof. Replacing `decide` with `scalar_tac` discharged that remaining inequality.
All subsequent definition contracts passed within the existing repair limit.

# Step 3.7 results

Completed 2026-11-13. Results/Store publishes 18 store contracts, imported by
Main and included in the headline audit. The wrappers retain the internal
statements exactly. Public documentation now describes established and preserved
store invariants, issued handles, allocator and memory premises, and same-length
memory write-back. Type compatibility remains a checked rejection condition.
Native platform wrappers and callback-specific host obligations remain explicit.

The combined Main import exposed a duplicate decodeExternal helper from step
3.5. Exports now imports and reuses the existing linking helper; its statements
are unchanged. Targeted checks, cached integration (4,065 jobs), lint, links,
and audit pass, with no budget or metric ratchet increases.

All 34 headline theorems use only standard logical axioms. The original 16
entries are unchanged. Publishing the new statements expands the statement
cone: handwritten declarations 1,682 → 1,699 and lines 9,486 → 9,603;
SpecTec declarations 2,616 → 2,617 and lines 25,640 → 25,641; extracted
declarations 2,722 → 2,743 and lines 62,349 → 62,925. The new handwritten
entries are mutation/growth and retained-prefix relations, raw value decoding,
export lookup, and segment counts used by the contracts. This expands audited
coverage without adding axioms or changing the logical trust boundary.
Rust, generated definitions, and specification definitions are unchanged.

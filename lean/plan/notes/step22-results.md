# Step 2.2 results

The generated function model is split into six ordered partitions plus an
umbrella. All 1,708 original declaration chunks are byte-for-byte unchanged:
738 validator, 66 shared runtime, 314 compiler, 49 store, 491 interpreter,
and 50 instantiation chunks. Types and handwritten external models are unchanged.
The extraction pipeline runs split_funs.py after comment normalization, and
extract-check compares all seven function files plus Types.

## Import isolation and proof organization

The user authorized breaking the shared representation dependency identified
in step22-blocker.md. The slot-specific block moved from Representation.Values
to Interp.ValueSlots; its two direct consumers now import that module. Shared
runtime.value facts stay in Values. The existing initializerWidth and
compiler_width_eq declarations moved unchanged into Values so the slot proofs
reuse that equation rather than duplicate an unfolding of runtime.value.width.
No theorem statement changed.

Runtime equation generation is separated into Bytecode and Interp modules,
with an umbrella for existing execution consumers. Both modules pass under
default heartbeat limits, removing the old unlimited override. Validator and
compiler imports use narrower generated partitions. Store instantiation proofs
explicitly import FunsInstantiate where they mention its declarations.

The metrics checker now reads definitions from every function partition and
rejects transitive FunsInterp imports from the validator and compiler. Synthetic
positive/negative/cyclic graph checks passed; the real import graph passes.
The metrics retain 1,380 extra unfolding files and import depth 64. Handwritten
modules increase from 775 to 778. Short modules increase from 50 to 53 due to
the equation split and relocation of the width helper, as recorded in the plan;
heartbeat overrides decrease from 266 to 265. Other ratchets are unchanged.

## Validation

Both Cargo test configurations, just extract, just extract-check, targeted Lean
checks, language-server diagnostics for ValueSlots, lint, and the final clean
integration build passed. Splitter scratch tests cover exact chunk/header/order
preservation, deterministic output, and malformed-input rejection before writes.

| Clean build | Wall seconds | User seconds | System seconds | Jobs |
| --- | ---: | ---: | ---: | ---: |
| Before consolidation | 1998.60 | 8531.34 | 7985.91 | 5676 |
| After step 2.1 | 1057.94 | 5644.86 | 2505.30 | 4049 |
| After step 2.2 | 974.00 | 5701.85 | 2515.61 | 4058 |

This step reduces wall time a further 7.9%, with total CPU time essentially
unchanged (+0.8%). Across Phase 2, wall time falls 51.3% and CPU time 50.2%.
Each clean run preserved dependency caches and saved the previous project cache;
no other builds or extraction competed with the final benchmark.

The final audit passes: all 16 headline theorems use only standard logical
axioms. Statement-cone totals remain 1,682 handwritten declarations / 9,486
lines, 2,616 specification declarations / 25,640 lines, and 2,720 extracted
declarations / 62,484 lines. The only handwritten audit-row change relocates
initializerWidth from Compiler.Local.Initializer to Representation.Values.
The pipeline now includes the approved text-preserving splitter; there are no
new theorem assumptions or changes to the handwritten external/specification
trust boundary.

# Step 3.4 results

Completed 2026-11-13. StoreWrite proves contracts for set_global, set_table,
and memory_mut. Successful writes identify the requested object and exact
decoded global value or table-element update. Rejected ordinary writes retain
the original store. Memory write-back requires the same byte length and proves
the exact decoded memory update. Error callbacks preserve executable invariants
without assuming equality of hidden platform-buffer state.

StoreGrow covers memory and table growth, including wrong-store/type rejection,
the growth failure sentinel, exact raw growth effects, source-store extension,
and executable-invariant preservation. A shared Store.check.spec in the existing
DefineTable module avoids additional unfolding sites in both API modules.

LSP checks, targeted builds, cached integration (4,062 jobs), lint, links, and
audit pass. All five public contracts and the identity-check helper were checked
directly for axioms: only the three standard logical axioms. The source scanner
matched the word "opaque" in a buffer docstring; inspection confirmed this was
ordinary prose, not a declaration. The headline audit is byte-for-byte unchanged.
No metric ratchet worsened or resource limit increased. There are now 782
handwritten modules, with 356 added proof lines. No trust boundary changed;
Rust and extracted definitions were unchanged.

Compiling only the changed helper module did not refresh stale transitive
language-server imports; a coordinated dependent build was required. Subsequent
iteration used LSP and targeted checks. The user relaxed the general three-repair
stop for routine tactic and elaboration fixes. The remaining memory_mut tuple
reduction was solved with an explicit simp-only list, without weakening its
contract or changing elaboration limits.

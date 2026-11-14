# Step 5.1 results

Completed 2026-11-13. A single op.dead equation in LoweringEmpty replaces all
204 adjacent dead-branch unfold/rewrite pairs in 41 consumer files. The owner
is the consolidated successor of the plan's Lowering module. Every consumer
already imported it transitively; no imports or existing statements changed.
Positive branches and unmatched unfolds remain unchanged. The proof handles
the dispatcher once and uses only standard axioms.

The opcode dispatcher is now unfolded in 30 files, down from 52 after the
phase 2 consolidation. The metrics scanner also counts simp/rw unfold sites,
so this is broader than counting literal unfold commands. Across the changed
files, explicit op unfolds fall from 480 to 277 (204 removed, one owner added).
Compiler source shrinks by 194 lines. Extra unfolding duplication falls to
1357; broad simp occurrences fall to 8815.

LSP and the owner check pass; targeted compilation covers all 42 changed Lean
modules and their dependencies. Lint, links, and whitespace checks pass. Broad
integration and the headline audit are batched at the compiler-pilot checkpoint
under the user's approved validation schedule. No resource budget or trust
boundary changed, and all existing theorem statements are preserved.

During validation, idle MCP language-server sessions retained many large file
workers. Restarting only those verified project-specific server process groups
released memory; automatic tool reconnection passed. The active build and all
compiled caches were preserved.

Checkpoint validation: cached `just prove` passes all 4,069 jobs; `just lint`
and `just audit` pass. The headline audit is unchanged.

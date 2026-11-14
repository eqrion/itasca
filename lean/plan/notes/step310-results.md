# Step 3.10 results

Completed 2026-11-13. Examples/Runtime imports only Main and supplies closed
fresh-store, host-invocation, and empty-module compilation/instantiation examples.
The host example exhibits an actual successful definition of a [] → [] host
and applies InvocationBehaves with every hypothesis discharged. The empty
module has independent binary encoding, elaboration, typing, restrictions,
and CompileEligible evidence; compiler completeness produces an accepted
executable. Applying the instantiation contract proves normal return with the
executable invariant and source outcome (the example does not assert an Ok
instantiation result).

The empty compiler demand reduces to zero function demand, one initializer
instruction, and allocation requests bounded by four. Its complete eligibility
proof passed; remaining edits were scalar simplification and explicit simp lists.
A shared header-size bound lives in CompileTotal, its existing constant-unfold
site. A new define_host_available lemma in StoreDefine derives successful host
creation from allocator availability and explicit object/signature headroom.
It preserves the existing API statements and unfolding boundary.

The former TrapHost example is consolidated into Runtime. Its reusable callback
and allocator witnesses move to Integration/Host/TrapWitness, which Main exports
alongside the new memory and float witnesses. This avoids an import cycle and
keeps the short-module count unchanged.

LSP, targeted compilation, cached integration (4,068 jobs), lint, links, and
headline audit pass. Direct checks of the closed examples, eligibility, and host
availability report only standard axioms with no source-scan warnings. This
checkpoint also completes broad validation for steps 3.8 and 3.9. The headline
statement cone is unchanged; every one of the 34 headlines retains standard
axioms. No metric ratchet, resource budget, generated definition, or logical
trust boundary changed.

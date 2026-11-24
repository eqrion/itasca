# Store operation and instantiation proofs

Store proofs track decoded objects, issued identities/handles/values, source
typing, segment accounting and compiled function capacities. Semantic definitions
are reached through [Interface/Store](../../Results/Definitions/Runtime.lean#L1066).

- `Invariant/` establishes retained metadata, ownership and code properties.
- `Api/` proves individual issued-object operations and growth effects.
- `Linking/` resolves imports against the issued store.
- `Preparation/` stages allocations and unpublished objects.
- `Initialization/` proves initializer and segment effects.
- `Instantiation/` joins the stages with publication and start-handle resolution.

Lower store subjects cannot import final instantiation. Rejection before
publication rolls back; segment traps retain completed initialization effects.
The returned start handle is invoked separately. The
[runtime guide](../README.md#interpreter-execution-integration-and-store) follows
these dependencies; public claims remain under Results.

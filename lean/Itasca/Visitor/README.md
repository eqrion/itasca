# Callback contracts and recorded execution

This layer gives the full visitor's normal-return and acceptance contracts and
relates callback-bearing execution to plain validation. [Total](Total.lean)
allows callbacks to reject; [Accepts](Total.lean) states the stronger successful
callback premise used for completeness. Normal return and acceptance are distinct.

[Events](RunTrace.lean), [EventTables](EventTables.lean) and
[RunTrace](RunTrace.lean) connect dispatched instructions, observations and
recorded runs. [BodyReplay](BodyReplay.lean) supplies replay facts. Public event
and recording vocabulary lives in
[Results/Definitions/Visitor](../Results/Definitions/Visitor.lean).

The public trace guarantees use an arbitrary observation function satisfying
`Records`. Construction helpers stay here: `Visitor.Trace.ofHandler` in `Events` builds a visitor from a handler, and `RunTrace` defines the
logging wrapper and accepting recorder. Their body-level convenience results
are in [Body/Trace/Acceptance](../Body/Trace/BytesDispatch.lean):
`instrument_body_trace`, `recorder_body_total`, and `recorder_body_complete`.
These helpers remain checked but are not part of interpreting a public trace
statement.

Callbacks observe instruction-body-relative positions. Their semantic meaning
must be specified independently of dispatch so correspondence proofs can detect
an incorrect callback mapping. This layer remains independent of runtime proofs.

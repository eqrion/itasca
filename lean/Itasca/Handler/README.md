# Validator operation contracts

Handler proofs describe individual extracted operand, control and environment
operations. [StackEffects](StackEffects.lean) relates concrete operand segments,
including polymorphic bottom values, to declarative stack types.
[ScalarOperations](ScalarOperations.lean) covers numeric, constant and select
contracts. [ScalarCompleteness](ScalarCompleteness.lean) constructs successful
scalar and environment handlers from independent premises.
[Environment](Environment.lean) and [EnvironmentDispatch](ScalarCompleteness.lean)
cover index lookups, control bases and environment-dependent dispatch.

Contracts establish normal return and success/error effects. Body preservation
and completeness combine them with independent encoding and typing evidence.
Handler may use Visitor and foundations plus narrow public definitions; it
cannot depend on body-loop or runtime constructions.

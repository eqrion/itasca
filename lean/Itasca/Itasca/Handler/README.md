# Operand and environment operations

A pop from an unreachable operand stack can succeed with a polymorphic bottom value. [Stack effects](StackEffects.lean) relates this behavior to declarative stack typing. [Scalar operations](ScalarOperations.lean) applies the relation to numeric instructions, constants, and select. For the reverse direction, [scalar completeness](ScalarCompleteness.lean) constructs successful handler calls from typing and environment facts.

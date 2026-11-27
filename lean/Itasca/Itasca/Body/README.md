# From validator stacks to typed instructions

Each instruction step relates the validator’s operand and control stacks to the type of an independently encoded instruction sequence. Closing the outer frame turns that step invariant into the certificate for a whole body. Start at [Correctness](Correctness.lean) and follow the direction you need: soundness starts with an accepted run, completeness with bytes and a typing derivation. Normal return also covers malformed input and rejecting callbacks.

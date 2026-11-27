# Establishing the runtime protocol

[RuntimeContract](RuntimeContract.lean) chooses the concrete store invariant that implements the abstract public protocol. It assembles store operations, instantiation, and invocation under that same predicate. For calls that enter the host, follow [host observations](Host/Observation.lean) and [invocation](Invocation/): the final argument retains the actual events and accounts for code the host may have added during the call.

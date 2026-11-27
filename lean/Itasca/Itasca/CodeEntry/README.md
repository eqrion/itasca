# From a code entry to a function body

A code entry includes a size prefix and local declarations before its instruction bytes. Entry offsets are measured in the code region. Operator positions start at the instruction body. [Encoding](Encoding.lean) relates the framed bytes and locals to the function signature. [Validation](Validation.lean) lifts body acceptance to the entry, and [Trace](Trace.lean) relates its callbacks to the body observations.

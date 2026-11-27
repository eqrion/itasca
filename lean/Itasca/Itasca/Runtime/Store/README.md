# Instantiation and the store

[Linking](Linking/) resolves imports against issued objects. [Preparation](Preparation/) stages allocations before publication. Rejection at this point preserves the old store. During [initialization](Initialization/), a segment trap can retain earlier writes. On success, instantiation returns the resolved start handle for a separate invocation. The [public instantiation theorems](../../Results/Instantiate.lean) spell out the store visible in each case.

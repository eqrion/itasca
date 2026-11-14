# Step 2.2 dependency blocker

Resolved with the user-authorized proof reorganization: interpreter slot proofs
now live in `Runtime/Interp/ValueSlots.lean`, and compiler/validator imports no
longer reach generated interpreter functions. The original preflight finding
and restriction are recorded below.

Identified 2026-11-13, before changing generated sources or running another
integration build. Step 2.1 is complete and validated at `a0e4a0a0`.

The planned import isolation cannot hold without reorganizing handwritten
proofs. A concrete chain is:

```text
Itasca.Runtime.Compiler.Local.Lowering.Float.FloatValueEncoding
  → Itasca.Runtime.Representation.Values
  → runtime.interp.encode_slot / runtime.interp.decode_slot
  → planned Itasca.Generated.FunsInterp
```

The compiler module directly imports Representation.Values. In that file,
`encode_slot_spec` (line 374) and `decode_slot_spec` (line 404) mention the
interpreter functions in their theorem statements, and their proofs unfold
those functions. These are in the final `Values` section, separate from the
earlier shared `StackLayout`, `Collection`, and `Encoding` sections.

Changing Equations imports cannot remove these required declarations. Splitting
the generated declarations unchanged puts both functions in FunsInterp by the
plan's classification, so the compiler would still transitively import it.
This is stronger evidence than a missing-import error; no full rebuild is
needed to establish the dependency.

Step 2.2 says to stop when a compiler proof still needs FunsInterp and explicitly
says not to restructure proofs to break the chain. Execution is paused before
performing the generated split, avoiding a costly partial rebuild whose target
import check cannot pass. No theorem, generated definition, or import was
changed for this step.

A possible bounded plan amendment is to separate the interpreter slot proofs
from the shared representation definitions, updating their consumers without
changing theorem statements. That requires authorization to relax step 2.2's
restriction; other dependencies would then still need checking. A splitter and
Makefile draft was prepared and scratch-tested, but is not part of the checked
step 2.1 checkpoint.

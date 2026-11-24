# Checked uses of public guarantees

These examples instantiate public Results theorems with concrete modules,
instruction bodies and host/store witnesses. They exercise how a consumer obtains
acceptance, metadata, compiled-code certificates and conditional execution claims.
They are part of the integrated Lean build.

Examples may import [Main](../Main.lean), the full Interface and Results. Lower
implementation layers cannot import examples. A satisfiable witness or passing
example supports use of a theorem; it does not replace checking that theorem's
full premises. Start with [module basics](Module/Basic.lean) after reading the
[public audit guide](../Results/README.md).

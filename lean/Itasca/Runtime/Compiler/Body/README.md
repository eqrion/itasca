# Whole-body compiler construction

Body proofs join independent instruction syntax, validator reader effects and
compiler callbacks into function code certificates. Reader replay retains exact
source operands and coordinates. Structured-control proofs account for live and
dormant scopes, labels, forward targets, branch tables and root closure.

`Reader/` organizes instruction families and their replay, acceptance, safety,
checking and publication arguments. `Body.Control/` composes structured prefixes and
control maps. `Relations/` assembles complete function and initializer evidence.
Acceptance proofs construct an actual successful run from source and resource
premises; they do not assume a completed callback trace.

The public code/capacity relations live in
[Results/Definitions/Compiler/Body](../../../Results/Definitions/README.md).
Body can use [Local](../Local/README.md), but cannot import Module or extracted
interpreter functions, including transitively. [Module](../Module/README.md)
combines these certificates with entry parsing and the complete-module driver.

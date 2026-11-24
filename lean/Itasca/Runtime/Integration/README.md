# Joined execution constructions

Integration combines compiler certificates, store preservation, interpreter
simulation, host laws and source resource demand. It constructs the public
guarantees rather than defining a second public API. The public retained
invariant and outcome vocabulary live under
[Results/Definitions/Integration](../../Results/Definitions/README.md).

`Api/` derives source typing and invariant preservation. `Execution/` assembles
operation outcomes, store mutation, ownership, histories, evolving code worlds
and resource causes. `Compilation/`, `Instantiation/`, `Invocation/` and `Host/`
join the relevant constructions. Public Results modules expose their conclusions.

Start with the [runtime reading paths](../README.md#reading-paths), then follow
the short proof of the chosen [public result](../../Results/README.md).
Retain actual recorded host events and final code interpretations throughout;
fixed-code or event-erased intermediate arguments do not replace the final
evolving-world theorem.

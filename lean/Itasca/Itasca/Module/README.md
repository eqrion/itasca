# Assembling a validated module

The validator processes the environment, code entries, and tail separately. [Layout](Layout.lean) ties their certificates to a single raw module, so the typing witness describes the same bytes as the returned metadata. Follow [elaboration](Elab/) for the passage from raw syntax to SpecTec typing, or [code framing](Code/Framing.lean) for the boundaries between entries.

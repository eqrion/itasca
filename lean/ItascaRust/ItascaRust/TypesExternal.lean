-- Value model for immutable shared metadata; see the trust boundary in README.md.
module
public import Aeneas
@[expose] public section

namespace Aeneas.Std.alloc.sync

/-- All strong references to this immutable allocation observe the same value. -/
@[rust_type "alloc::sync::Arc"]
abbrev Arc (T : Type) := T

end Aeneas.Std.alloc.sync

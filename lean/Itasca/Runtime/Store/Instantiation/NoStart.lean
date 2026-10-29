import Itasca.Runtime.Equations
import Itasca.Runtime.Store.Initialization.SegmentInitializePreservation

/-!
Structural store validity provides the finite constant-read bindings needed by the compiler's synthetic initialization code.

Main declarations: `Shape.initializer_bindings`. A direct consumer is `Integration.Instantiation.StartResolution`.
-/

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Structural store validity provides the finite constant-read bindings needed
by the compiler's synthetic initialization code. -/
theorem Shape.initializer_bindings {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (shape : Shape view store) (found : inst ∈ store.instances.val) :
    InitializerBindings store inst := by
  have instanceShape := shape.instances inst found
  refine ⟨?_, shape.globals⟩
  intro address member
  exact (instanceShape.2.2.2.2.2.2.2.2.1 address member).2

end Itasca.Runtime.Store

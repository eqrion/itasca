import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Theorems.Host.Open.Driver.DriverTick
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Checked local effects give the same cross-world effect used by suspended
callers, with unchanged code and external-reference issuance. -/
theorem local_effect_world {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {before after : runtime.store.Store M} (effect : OpenHostControl.Effect view code before after) :
    ReentrantCallbacks.Effect view code before code after :=
  ⟨⟨(by intro index inst found fn; rfl),effect.invariant,effect.metadata,effect.extension⟩,by rw [effect.externs]⟩

end Exec.Theorems.OpenReentrantControl

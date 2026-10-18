import Exec.Theorems.Composition.Core.CoreStepCertified
import Exec.Store.Invariant.InstantiationCode
import Exec.Store.Initialization.SegmentObjectMetadata
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Function allocation only appends defined Wasm entries; content staging and
publication cannot introduce a host into a defined-only store. -/
theorem CoreHostFree.instantiation {M : Type} {before after : runtime.store.Store M}
    {inst : runtime.store.Instance} (free : CoreHostFree before)
    (metadata : Store.InstantiationCode before after inst) : CoreHostFree after := by
  obtain ⟨staged,count,rfl,retained,entries,table,signatures⟩ := metadata
  intro function member host
  rcases signatures function member with old | ⟨index,bound,wasm,signature⟩
  · exact free function old host
  · rw [wasm]
    intro impossible
    cases impossible

theorem CoreHostFree.frame_metadata {M : Type} {before after : runtime.store.Store M}
    (free : CoreHostFree before) (metadata : Interp.FrameStoreMetadata before after) : CoreHostFree after := by
  simpa only [CoreHostFree,metadata.functions] using free

end Exec.Theorems

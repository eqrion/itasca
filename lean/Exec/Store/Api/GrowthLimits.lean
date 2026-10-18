import Exec.Store.Api.GrowthEffects
namespace Exec.Store
open Aeneas Aeneas.Std

theorem MemoryGrowth.limits {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {before : runtime.store.Store M} {index delta out} (effect : MemoryGrowth view code before index delta out) :
    out.2.limits = before.limits := by
  rcases effect with ⟨_,_,same | ⟨old,buffer,lookup,viewEq,same⟩⟩ |
    ⟨old,buffer,count,lookup,bytes,used,limit,capacity,maximum,size,same⟩
  all_goals rw [same]

theorem TableGrowth.limits {M : Type} {before : runtime.store.Store M} {index delta value out}
    (effect : TableGrowth before index delta value out) : out.2.limits = before.limits := by
  rcases effect with ⟨_,same⟩ | ⟨old,words,count,lookup,values,capacity,used,limit,maximum,same⟩
  all_goals rw [same]
end Exec.Store

import Itasca.Runtime.Store.Invariant.ValueDecode
import Itasca.Runtime.Store.Api.Grow

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Raw reference words fit the machine index type because they refer to a
retained object; zero remains the separate null sentinel. -/
theorem ReferenceShape.word_bound {M : Type} (s : runtime.store.Store M)
    (ty : Itasca.types.ElemType) (word : U64) (h : ReferenceShape s ty word) :
    word.val ≤ Usize.max := by
  rcases h with hzero | hindex
  · scalar_tac
  · cases ty <;> dsimp at hindex <;> scalar_tac

/-- Decoding canonical store words restores an owned API reference with an
existing address. This establishes the caller invariant for values obtained
through global and table accessors. -/
theorem decode_global_owned {M : Type} (s : runtime.store.Store M)
    (global : runtime.store.GlobalInst) (hg : GlobalShape s global) :
    runtime.value.decode global.ty.valtype global.lo global.hi s.id ⦃ value => ValueInStore s value ⦄ := by
  cases ht : global.ty.valtype <;> simp only [runtime.value.decode, ht]
  all_goals simp [lift, ValueInStore, Interp.ValueOwnedFits]
  case V128 => step
  case FuncRef =>
    simp only [GlobalShape, ht] at hg
    split
    · simp
    · rename_i hn
      have hbound := hg.1.word_bound s .FuncRef global.lo
      have hcast := cast_usize_exact global.lo hbound
      have hindex : global.lo.val - 1 < s.funcs.length := by
        rcases hg.1 with hz | hi
        · scalar_tac
        · exact hi
      step as ⟨index, hindexValue⟩
      scalar_tac
  case ExternRef =>
    simp only [GlobalShape, ht] at hg
    split
    · simp
    · rename_i hn
      have hbound := hg.1.word_bound s .ExternRef global.lo
      have hcast := cast_usize_exact global.lo hbound
      have hindex : global.lo.val - 1 < s.externs.length := by
        rcases hg.1 with hz | hi
        · scalar_tac
        · exact hi
      step as ⟨index, hindexValue⟩
      scalar_tac

end Itasca.Runtime.Store

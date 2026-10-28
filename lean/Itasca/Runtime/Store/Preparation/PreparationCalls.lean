import Itasca.Runtime.Store.Invariant.NormalResult
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- A finite prefix of actual successful preparation calls. This records the
reached store/map inputs of a later refusal, rather than an arbitrary store
with a conveniently exceeded quota. -/
inductive PreparationCalls {S : Type}
    (call : S → Usize → Result (core.result.Result Unit runtime.ExecError × S)) :
    S → Usize → S → Usize → Prop where
  | refl (state : S) (index : Usize) : PreparationCalls call state index state index
  | next {initial current after : S} {start index nextIndex : Usize}
      (prior : PreparationCalls call initial start current index)
      (called : call current index = .ok (.Ok (),after))
      (advanced : nextIndex.val = index.val + 1) :
      PreparationCalls call initial start after nextIndex

end Itasca.Runtime.Store

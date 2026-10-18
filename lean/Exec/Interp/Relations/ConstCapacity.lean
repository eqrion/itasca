import Exec.Interp.Control.StructuredLinear
import Exec.Interp.Relations.ConstCertified
import Exec.Interp.Relations.Capacity

namespace Exec.Code
open Aeneas Aeneas.Std

/-- The checked constant destination fits even when its source point is behind
one or more administrative forward jumps. -/
theorem const32_capacity
    (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (types functions : List functype) (returns locals stack : List valtype)
    (labels : List LabelTarget) (value : U32) (after : List instr)
    (next : Nat) (output : List valtype) :
    ∀ pc, CodeRel types functions returns locals compiled.code.val labels stack
      (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after) pc next output →
      slots locals + slots stack < compiled.slot_count.val := by
  intro pc relation
  generalize measureEq : compiled.code.val.length - pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases Interp.codeRel_linear_inv (by rfl) relation with skip | branch
    · obtain ⟨target, forward, fetched, continuation⟩ := skip
      have targetBound := continuation.entry_bound
      exact ih (compiled.code.val.length - target.val) (by omega) target.val continuation rfl
    · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
      obtain ⟨dst, emittedEq, middleEq, position⟩ := Interp.linearEmission_const32_inv value head
      have fetched : compiled.code.val[pc]? = some (.Const32 dst value) := by
        simpa only [Nat.add_zero] using fragment.fetch (index := 0)
          (by simp only [emittedEq, List.getElem?_cons_zero])
      have bound := const32_valid_bounds compiled dst value (well_formed_fetched compiled checked pc _ fetched)
      simpa only [position] using bound

/-- The checked constant destination fits even when its source point is behind
one or more administrative forward jumps. -/
theorem const64_capacity
    (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (types functions : List functype) (returns locals stack : List valtype)
    (labels : List LabelTarget) (value : U64) (after : List instr)
    (next : Nat) (output : List valtype) :
    ∀ pc, CodeRel types functions returns locals compiled.code.val labels stack
      (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after) pc next output →
      slots locals + slots stack < compiled.slot_count.val := by
  intro pc relation
  generalize measureEq : compiled.code.val.length - pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases Interp.codeRel_linear_inv (by rfl) relation with skip | branch
    · obtain ⟨target, forward, fetched, continuation⟩ := skip
      have targetBound := continuation.entry_bound
      exact ih (compiled.code.val.length - target.val) (by omega) target.val continuation rfl
    · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
      obtain ⟨dst, emittedEq, middleEq, position⟩ := Interp.linearEmission_const64_inv value head
      have fetched : compiled.code.val[pc]? = some (.Const64 dst value) := by
        simpa only [Nat.add_zero] using fragment.fetch (index := 0)
          (by simp only [emittedEq, List.getElem?_cons_zero])
      have bound := const64_valid_bounds compiled dst value (well_formed_fetched compiled checked pc _ fetched)
      simpa only [position] using bound

end Exec.Code
